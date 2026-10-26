//! One computer on the network: its iroh endpoint, its roster and the agents it offers.

mod directory;
mod inbound;
mod outbox;

use crate::guard::{self, Guard};
use crate::reach::{Held, Reach};
use crate::roster::{self, Change, Role, Roster};
use crate::rules::{self, Rule};
use crate::types::{Address, Connector, Letter, Message, Peer, Sent};
use crate::wire::{self, ALPN, Agent, Request, Response, Ticket};
use anyhow::{Context, Result, anyhow, bail};
use iroh::endpoint::{Connection, presets};
use iroh::protocol::Router;
use iroh::{Endpoint, EndpointAddr, EndpointId, RelayMode, RelayUrl, SecretKey, Watcher};
use std::collections::{HashMap, VecDeque};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, Weak};
use std::time::{Duration, Instant};
use tokio::sync::{mpsc, watch};
use tokio::task::JoinSet;

const KEY_FILE: &str = "secret.key";
/// How long an invite stays good.
pub const INVITE_FOR: Duration = Duration::from_hours(1);
const CONNECT_TIMEOUT: Duration = Duration::from_secs(10);
/// Long enough for the other computer to knock on its agent's harness.
const CALL_TIMEOUT: Duration = Duration::from_secs(20);
const INBOX_SIZE: usize = 256;
/// How long addresses get to settle after a change before this computer signs where it is.
const ADDR_SETTLE: Duration = Duration::from_secs(2);
/// Letters whose handoff count a reply may need, newest kept.
const HEARD_MAX: usize = 1000;

pub struct Node {
    inner: Arc<Inner>,
    router: Router,
}

struct Inner {
    endpoint: Endpoint,
    dir: PathBuf,
    roster: Mutex<Option<Roster>>,
    agents: Mutex<Vec<(Agent, Reach)>>,
    /// Names the app also sends as without offering them (`set_senders`).
    senders: Mutex<Vec<String>>,
    /// The app offered its agents since the node started: until then, letters wait at the sender.
    ready: AtomicBool,
    /// The handoff count of letters taken here, by id, so a reply carries the chain on.
    heard: Mutex<VecDeque<(String, u8)>>,
    /// What each other computer offered when it last answered or wrote.
    seen: Mutex<HashMap<EndpointId, directory::Seen>>,
    invites: Mutex<HashMap<String, Instant>>,
    guard: Mutex<Guard>,
    held: Mutex<Held>,
    /// Letters already taken, so a sender's retry isn't delivered twice.
    taken: Mutex<VecDeque<String>>,
    /// Who may write to this computer's agents (`rules`).
    rules: Mutex<Vec<Rule>>,
    /// Requests this computer sent, newest kept, and to whom: an answer to one passes the rules.
    asked: Mutex<VecDeque<(String, EndpointId)>>,
    outbox: Mutex<Vec<outbox::Queued>>,
    inbox: mpsc::Sender<Message>,
    /// The command an agent the network knocks on runs to answer.
    reply_command: Mutex<String>,
    /// Ticks when the members, their roles or names, or what the others offer or whether they
    /// answer, change.
    changed: watch::Sender<()>,
}

fn locked<T>(m: &Mutex<T>) -> MutexGuard<'_, T> {
    m.lock().unwrap_or_else(std::sync::PoisonError::into_inner)
}

impl Node {
    /// Starts this computer's node. State (its key and the roster) lives in `dir`. Messages for
    /// agents the app delivers to ([`Reach::App`]) come out of the returned inbox.
    pub async fn start(dir: &Path, connector: &Connector) -> Result<(Self, mpsc::Receiver<Message>)> {
        std::fs::create_dir_all(dir)?;
        let key = load_key(dir)?;
        let endpoint = bind(key, connector).await?;
        let (tx, rx) = mpsc::channel(INBOX_SIZE);
        let inner = Arc::new(Inner {
            endpoint: endpoint.clone(),
            dir: dir.to_path_buf(),
            roster: Mutex::new(Roster::load(dir)?),
            agents: Mutex::default(),
            senders: Mutex::default(),
            ready: AtomicBool::new(false),
            heard: Mutex::default(),
            seen: Mutex::default(),
            invites: Mutex::default(),
            guard: Mutex::default(),
            held: Mutex::default(),
            taken: Mutex::default(),
            rules: Mutex::default(),
            asked: Mutex::default(),
            outbox: Mutex::default(),
            inbox: tx,
            reply_command: Mutex::new("codync-network".into()),
            changed: watch::Sender::new(()),
        });
        let router = Router::builder(endpoint).accept(ALPN, inbound::Handler(inner.clone())).spawn();
        settle(&inner.endpoint, connector).await;
        inner.locate(inner.endpoint.addr())?;
        // Catch up with the others: a computer that was off may have missed a removal.
        inner.clone().hello_all();
        tokio::spawn(outbox::retry_loop(Arc::downgrade(&inner)));
        tokio::spawn(follow_addr(Arc::downgrade(&inner), inner.endpoint.watch_addr()));
        Ok((Self { inner, router }, rx))
    }

    pub fn id(&self) -> EndpointId {
        self.inner.endpoint.id()
    }

    /// This computer's name, once it is in a network.
    pub fn name(&self) -> Option<String> {
        locked(&self.inner.roster).as_ref().map(|r| r.name(&self.id()))
    }

    pub fn role(&self) -> Option<Role> {
        locked(&self.inner.roster).as_ref().and_then(|r| r.role(&self.id()))
    }

    /// Starts a new network with this computer as its owner. Returns the recovery code: show it
    /// once; it is kept nowhere.
    pub fn create(&self, name: &str) -> Result<String> {
        let mut roster = locked(&self.inner.roster);
        if roster.is_some() {
            bail!("this computer is already in a network");
        }
        let key = self.inner.endpoint.secret_key();
        let (new, root) = Roster::create(key, check_name(name)?, self.inner.endpoint.addr(), wire::now_ms());
        self.inner.save(&new)?;
        *roster = Some(new);
        Ok(roster::recovery_code(&root))
    }

    /// A one-time invite for another computer, good for an hour while this one stays on.
    pub fn invite(&self) -> Result<String> {
        let roster = self.inner.roster()?;
        if !roster.role(&self.id()).is_some_and(Role::invites) {
            bail!("only the owner and admins can invite computers");
        }
        let secret = wire::random_hex(16);
        locked(&self.inner.invites).insert(secret.clone(), Instant::now() + INVITE_FOR);
        Ticket { network: roster.network, secret, addr: self.inner.endpoint.addr() }.encode()
    }

    pub async fn join(&self, ticket: &str, name: &str) -> Result<()> {
        if locked(&self.inner.roster).is_some() {
            bail!("this computer is already in a network");
        }
        let ticket = Ticket::decode(ticket)?;
        let request = Request::Join { network: ticket.network, secret: ticket.secret, name: check_name(name)? };
        let conn = tokio::time::timeout(CONNECT_TIMEOUT, self.inner.endpoint.connect(ticket.addr, ALPN))
            .await
            .context("the inviting computer didn't answer; is it on?")??;
        let answer = wire::call(&conn, &request).await;
        conn.close(0u32.into(), b"done");
        match answer? {
            Response::Welcome { roster } if roster.network == ticket.network => {
                let mut roster = roster.verified();
                if !roster.is_member(&self.id()) {
                    bail!("the inviting computer gave an unexpected answer");
                }
                // Where this computer is; nothing to add when it knows no address yet.
                let addr = self.inner.endpoint.addr();
                let _ = roster.sign(self.inner.endpoint.secret_key(), wire::now_ms(), Change::Locate { addr });
                // Held across saving and keeping it, so whoever `changes` wakes sees it.
                let mut guard = locked(&self.inner.roster);
                self.inner.save(&roster)?;
                *guard = Some(roster);
                drop(guard);
                self.inner.clone().hello_all();
                Ok(())
            }
            Response::Refused { reason } => bail!("{reason}"),
            _ => bail!("the inviting computer gave an unexpected answer"),
        }
    }

    /// Takes a computer out of the network for good. `cascade` also voids every computer it
    /// admitted: for one that was stolen.
    pub fn remove(&self, computer: &str, cascade: bool) -> Result<()> {
        let id = self.inner.member(computer)?;
        if id == self.id() {
            bail!("a computer can't remove itself; remove it from another one");
        }
        self.inner.change(Change::Remove { id, cascade }, "only the owner removes admins; admins remove members")
    }

    /// The owner makes a computer an admin: it can invite and remove members.
    pub fn promote(&self, computer: &str) -> Result<()> {
        let id = self.inner.member(computer)?;
        self.inner.change(Change::Promote { id }, "only the owner promotes computers")
    }

    /// Makes this computer the owner with the network's recovery code, for when the owner was
    /// lost. Remove the old one afterwards.
    pub fn recover(&self, code: &str) -> Result<()> {
        let root = roster::root_from_code(code)?;
        let mut guard = locked(&self.inner.roster);
        let roster = guard.as_mut().ok_or_else(|| anyhow!("this computer isn't in a network"))?;
        if root.public() != roster.network {
            bail!("that recovery code is for another network");
        }
        let name = roster.name(&self.id());
        roster.sign(&root, wire::now_ms(), Change::Owner { id: self.id(), name })?;
        self.inner.save(roster)?;
        drop(guard);
        self.inner.clone().hello_all();
        Ok(())
    }

    /// What this computer offers. The first call opens it to letters, and the others hear at once,
    /// so what waited for it while it started comes now.
    pub fn set_agents(&self, agents: impl IntoIterator<Item = (Agent, Reach)>) {
        let before = self.inner.offered();
        *locked(&self.inner.agents) = agents.into_iter().collect();
        if self.inner.offered() != before {
            self.inner.changed.send_replace(());
        }
        if !self.inner.ready.swap(true, Ordering::AcqRel) {
            self.inner.clone().hello_all();
        }
    }

    /// Names the app sends letters as without offering them to the network: a hosted assistant that
    /// asks agents elsewhere but can't be asked itself. Answers to its letters still come back.
    pub fn set_senders(&self, senders: impl IntoIterator<Item = String>) {
        *locked(&self.inner.senders) = senders.into_iter().collect();
    }

    /// Who on the other computers may write to this computer's agents, the first match deciding.
    /// Answers to this computer's own letters always pass, so a rule added while a request runs
    /// doesn't strand it.
    pub fn set_rules(&self, rules: Vec<Rule>) -> Result<()> {
        rules::check_all(&rules)?;
        *locked(&self.inner.rules) = rules;
        Ok(())
    }

    pub fn rules(&self) -> Vec<Rule> {
        locked(&self.inner.rules).clone()
    }

    /// The command agents the network knocks on run to reply (default `codync-network`).
    pub fn set_reply_command(&self, command: impl Into<String>) {
        *locked(&self.inner.reply_command) = command.into();
    }

    /// Every computer in the network, asked now for what it offers.
    pub async fn peers(&self) -> Result<Vec<Peer>> {
        let roster = self.inner.roster()?;
        let mut asks = JoinSet::new();
        for id in roster.members().keys().filter(|id| **id != self.id()).copied() {
            let inner = self.inner.clone();
            asks.spawn(async move { inner.hello(id).await });
        }
        while asks.join_next().await.is_some() {}
        Ok(self.directory())
    }

    /// Every computer in the network, as last heard, without asking anyone.
    pub fn directory(&self) -> Vec<Peer> {
        self.inner.directory()
    }

    /// Changes whenever what [`Node::directory`] shows does: a computer joins or leaves, a role
    /// or name changes, another computer offers different agents, or it starts or stops
    /// answering. Ticks only; read the directory for what changed.
    pub fn changes(&self) -> watch::Receiver<()> {
        self.inner.changed.subscribe()
    }

    /// Where a bare agent name or a full `agent@computer` points: this computer first, then the
    /// directory. Refuses a name more than one computer has, naming them.
    pub fn resolve(&self, name: &str) -> Result<Address> {
        self.inner.resolve(name)
    }

    /// Sends a letter from one of the agents this computer offers. An answer (`reply_to`) may also
    /// come from one it no longer offers: renamed or gone while it worked, it still says how it ended.
    pub async fn send(&self, letter: Letter) -> Result<Sent> {
        let sender = |from: &str| {
            self.inner.offered().iter().any(|a| a.id == from) || locked(&self.inner.senders).iter().any(|s| s == from)
        };
        if letter.reply_to.is_none() && !sender(&letter.from) {
            bail!("{} isn't one of this computer's agents", letter.from);
        }
        // A reply carries on the chain of the letter it answers (one more handoff).
        let mut letter = letter;
        if letter.hops == 0
            && let Some(hops) = letter.reply_to.as_deref().and_then(|id| self.inner.hops_of(id))
        {
            letter.hops = hops.saturating_add(1);
        }
        guard::check_hops(letter.hops).map_err(anyhow::Error::msg)?;
        let roster = locked(&self.inner.roster).clone();
        let id = match &roster {
            None => self.id(),
            Some(r) => {
                r.find(&letter.to.computer).ok_or_else(|| anyhow!("no computer called {}", letter.to.computer))?
            }
        };
        let local = id == self.id();
        let envelope = letter.seal(wire::now_ms());
        wire::check(&envelope)?;
        // A request, which an answer may come back to past the other computer's rules.
        if !local && envelope.wake && envelope.reply_to.is_none() {
            self.inner.asked(&envelope.id, id);
        }
        let name = |id: &EndpointId| roster.as_ref().map_or_else(|| "this computer".into(), |r| r.name(id));
        let answer = if local {
            Ok(self.inner.take(id, envelope.clone()).await)
        } else {
            self.inner.call(id, &Request::Deliver { envelope: envelope.clone() }).await
        };
        match answer {
            Ok(Response::Stored) => Ok(Sent::Delivered),
            Ok(Response::Refused { reason }) => bail!("{} refused it: {reason}", name(&id)),
            Ok(Response::Later { reason }) if local => bail!("{reason}"),
            Ok(Response::Later { reason }) => {
                tracing::info!(to = %name(&id), reason, "queued for a computer that is starting");
                self.inner.queue(id, envelope)?;
                Ok(Sent::Queued)
            }
            Ok(_) => bail!("{} gave an unexpected answer", name(&id)),
            Err(e) => {
                tracing::info!(to = %name(&id), error = format!("{e:#}"), "queued for a computer that is away");
                self.inner.queue(id, envelope)?;
                Ok(Sent::Queued)
            }
        }
    }

    pub async fn shutdown(self) {
        let _ = self.router.shutdown().await;
    }
}

impl Inner {
    fn roster(&self) -> Result<Roster> {
        locked(&self.roster).clone().ok_or_else(|| anyhow!("this computer isn't in a network yet"))
    }

    fn me(&self) -> EndpointId {
        self.endpoint.id()
    }

    fn asked(&self, letter: &str, to: EndpointId) {
        let mut asked = locked(&self.asked);
        if asked.len() >= HEARD_MAX {
            asked.pop_front();
        }
        asked.push_back((letter.to_owned(), to));
    }

    /// Whether a letter from `peer` answers one this computer sent it.
    pub(super) fn answers(&self, peer: EndpointId, reply_to: Option<&str>) -> bool {
        reply_to.is_some_and(|id| locked(&self.asked).iter().any(|(sent, to)| sent == id && *to == peer))
    }

    fn hops_of(&self, letter: &str) -> Option<u8> {
        locked(&self.heard).iter().rev().find(|(id, _)| id == letter).map(|(_, hops)| *hops)
    }

    fn heard(&self, letter: &str, hops: u8) {
        let mut heard = locked(&self.heard);
        if heard.len() >= HEARD_MAX {
            heard.pop_front();
        }
        heard.push_back((letter.to_owned(), hops));
    }

    fn offered(&self) -> Vec<Agent> {
        locked(&self.agents).iter().map(|(agent, _)| agent.clone()).collect()
    }

    fn member(&self, computer: &str) -> Result<EndpointId> {
        self.roster()?.find(computer).ok_or_else(|| anyhow!("no computer called {computer}"))
    }

    /// Signs `change` as this computer, saves it and tells the others.
    fn change(self: &Arc<Self>, change: Change, refused: &str) -> Result<()> {
        let mut guard = locked(&self.roster);
        let roster = guard.as_mut().ok_or_else(|| anyhow!("this computer isn't in a network"))?;
        roster.sign(self.endpoint.secret_key(), wire::now_ms(), change).map_err(|_| anyhow!("{refused}"))?;
        self.save(roster)?;
        drop(guard);
        self.clone().hello_all();
        Ok(())
    }

    /// Writes where this computer is into the roster when it moved. Returns whether it did.
    fn locate(&self, addr: EndpointAddr) -> Result<bool> {
        let mut guard = locked(&self.roster);
        let Some(roster) = guard.as_mut() else { return Ok(false) };
        if roster.members().get(&self.me()).is_none_or(|m| m.addr == addr) {
            return Ok(false);
        }
        roster.sign(self.endpoint.secret_key(), wire::now_ms(), Change::Locate { addr })?;
        self.save(roster)?;
        Ok(true)
    }

    /// Keeps `roster` on disk and tells whoever watches [`Node::changes`]. Callers hold the roster
    /// lock until `roster` is the one kept in memory, so a watcher woken here reads it.
    fn save(&self, roster: &Roster) -> Result<()> {
        roster.save(&self.dir)?;
        self.changed.send_replace(());
        Ok(())
    }

    async fn connect(&self, id: EndpointId) -> Result<Connection> {
        let addr = locked(&self.roster)
            .as_ref()
            .and_then(|r| r.members().get(&id).map(|m| m.addr.clone()))
            .unwrap_or_else(|| EndpointAddr::new(id));
        // ponytail: a new connection per call; keep them open when traffic makes setup cost show.
        Ok(tokio::time::timeout(CONNECT_TIMEOUT, self.endpoint.connect(addr, ALPN)).await??)
    }

    async fn call(&self, id: EndpointId, request: &Request) -> Result<Response> {
        let conn = self.connect(id).await?;
        let answer = tokio::time::timeout(CALL_TIMEOUT, wire::call(&conn, request)).await;
        conn.close(0u32.into(), b"done");
        answer?
    }

    /// Swaps rosters and agent lists with one member.
    async fn hello(self: &Arc<Self>, id: EndpointId) -> Result<Vec<Agent>> {
        let request = Request::Hello { roster: self.roster()?, agents: self.offered() };
        let answer = self.call(id, &request).await;
        let agents = match answer {
            Ok(Response::Hello { roster, agents }) => {
                self.merge(&roster)?;
                self.clone().flush(id);
                agents
            }
            Ok(Response::Refused { reason }) => {
                self.saw(id, None);
                bail!("{reason}")
            }
            Ok(_) => bail!("unexpected answer"),
            Err(e) => {
                self.saw(id, None);
                return Err(e);
            }
        };
        self.saw(id, Some(agents.clone()));
        Ok(agents)
    }

    /// Says hello to every other member in the background, so a change reaches them.
    fn hello_all(self: Arc<Self>) {
        let Ok(roster) = self.roster() else { return };
        let me = self.me();
        for id in roster.members().keys().copied().filter(|id| *id != me) {
            let inner = self.clone();
            tokio::spawn(async move {
                if let Err(e) = inner.hello(id).await {
                    tracing::debug!(peer = %id.fmt_short(), error = format!("{e:#}"), "hello didn't get through");
                }
            });
        }
    }

    fn merge(&self, theirs: &Roster) -> Result<()> {
        let mut guard = locked(&self.roster);
        let Some(mine) = guard.as_mut() else { return Ok(()) };
        if mine.merge(theirs) {
            self.save(mine)?;
        }
        Ok(())
    }
}

/// Signs where this computer is again whenever its addresses change (a laptop that moved to
/// another network) and tells the others, so they find it without a restart: with the `private`
/// connector, nothing else would. The roster keeps only each computer's newest location.
async fn follow_addr(inner: Weak<Inner>, mut addr: impl Watcher<Value = EndpointAddr>) {
    while addr.updated().await.is_ok() {
        // Addresses change in bursts (an interface comes up, then the relay answers): sign once.
        tokio::time::sleep(ADDR_SETTLE).await;
        let Some(inner) = inner.upgrade() else { return };
        match inner.locate(addr.get()) {
            Ok(true) => {
                tracing::info!("this computer moved; telling the others");
                inner.hello_all();
            }
            Ok(false) => {}
            Err(e) => tracing::warn!(error = format!("{e:#}"), "couldn't sign where this computer is"),
        }
    }
}

async fn bind(key: SecretKey, connector: &Connector) -> Result<Endpoint> {
    let builder = match connector {
        Connector::Public => Endpoint::builder(presets::N0),
        Connector::Relay(url) => {
            let url: RelayUrl = url.parse().context("not a relay URL")?;
            Endpoint::builder(presets::Minimal).relay_mode(RelayMode::custom([url]))
        }
        Connector::Private => Endpoint::builder(presets::Minimal).relay_mode(RelayMode::Disabled),
    };
    Ok(builder.secret_key(key).bind().await?)
}

/// Waits briefly until the endpoint knows its own addresses, so invites and the roster carry them.
async fn settle(endpoint: &Endpoint, connector: &Connector) {
    if *connector != Connector::Private {
        let _ = tokio::time::timeout(Duration::from_secs(5), endpoint.online()).await;
    }
    let until = Instant::now() + Duration::from_secs(3);
    while endpoint.addr().ip_addrs().next().is_none() && Instant::now() < until {
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
}

fn load_key(dir: &Path) -> Result<SecretKey> {
    let path = dir.join(KEY_FILE);
    match std::fs::read(&path) {
        Ok(bytes) => {
            let bytes: [u8; 32] = bytes.try_into().map_err(|_| anyhow!("{} is damaged", path.display()))?;
            Ok(SecretKey::from_bytes(&bytes))
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            let key = SecretKey::generate();
            write_private(&path, &key.to_bytes())?;
            Ok(key)
        }
        Err(e) => Err(e).context("couldn't read this computer's key"),
    }
}

fn write_private(path: &Path, bytes: &[u8]) -> Result<()> {
    #[cfg(unix)]
    {
        use std::io::Write;
        use std::os::unix::fs::OpenOptionsExt;
        let mut file = std::fs::OpenOptions::new().write(true).create_new(true).mode(0o600).open(path)?;
        file.write_all(bytes)?;
    }
    #[cfg(not(unix))]
    std::fs::write(path, bytes)?;
    Ok(())
}

fn check_name(name: &str) -> Result<String> {
    let name = name.trim();
    if name.is_empty() || name.len() > 40 || name.contains(['/', ' ', '@', '.']) {
        bail!("a computer's name is 1–40 characters, without spaces, /, @ or .");
    }
    Ok(name.into())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temp_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("codync-network-unit-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        dir
    }

    #[tokio::test]
    async fn a_computer_that_moves_tells_the_others_without_a_restart() {
        let (desk_dir, laptop_dir) = (temp_dir("desk"), temp_dir("laptop"));
        let (desk, _) = Node::start(&desk_dir, &Connector::Private).await.expect("desk starts");
        desk.create("desk").expect("a network");
        let (laptop, _) = Node::start(&laptop_dir, &Connector::Private).await.expect("laptop starts");
        laptop.join(&desk.invite().expect("an invite"), "laptop").await.expect("joined");

        // The laptop moves: an address it didn't have before.
        let moved = laptop.inner.endpoint.addr().with_ip_addr("192.0.2.7:4242".parse().expect("an address"));
        let watched = n0_watcher::Watchable::new(laptop.inner.endpoint.addr());
        tokio::spawn(follow_addr(Arc::downgrade(&laptop.inner), watched.watch()));
        watched.set(moved.clone()).expect("watched");
        let desk_sees =
            || locked(&desk.inner.roster).as_ref().and_then(|r| r.members().get(&laptop.id()).map(|m| m.addr.clone()));
        tokio::time::timeout(Duration::from_secs(10), async {
            while desk_sees() != Some(moved.clone()) {
                tokio::time::sleep(Duration::from_millis(50)).await;
            }
        })
        .await
        .expect("the desk hears where the laptop is now");
        for dir in [desk_dir, laptop_dir] {
            let _ = std::fs::remove_dir_all(dir);
        }
    }
}
