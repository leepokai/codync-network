//! Who is in the network: a log of signed changes that every member keeps a copy of.
//!
//! Copies merge (a union of entries), and every computer works out the same members from them,
//! whatever order the entries arrived in. Each entry is signed by the computer that made it, and
//! it counts only if that computer could make it:
//!
//! - the network's **root key** (the recovery code, kept on no computer) names the owner;
//! - the **owner** promotes admins, and admits and removes anyone;
//! - **admins** admit computers and remove plain members;
//! - every computer writes only where it is reachable.
//!
//! A removed computer stays removed: coming back means joining again with a new key.

use crate::wire;
use anyhow::{Context, Result, anyhow, bail};
use iroh::{EndpointAddr, EndpointId, SecretKey, Signature};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

const FILE: &str = "network.json";
/// Entries a copy may hold; one from far beyond that isn't a network of computers.
const MAX_ENTRIES: usize = 20_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum Role {
    Member,
    Admin,
    Owner,
}

/// One computer in the network, as the log has it now.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Member {
    pub name: String,
    pub role: Role,
    /// Where it last said it was reachable.
    pub addr: EndpointAddr,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum Change {
    /// The root key names the owner (again, to move it to another computer).
    Owner {
        id: EndpointId,
        name: String,
    },
    Admit {
        id: EndpointId,
        name: String,
    },
    Promote {
        id: EndpointId,
    },
    /// `cascade` also voids everything the removed computer signed (a stolen one).
    Remove {
        id: EndpointId,
        cascade: bool,
    },
    /// Where the signing computer is reachable.
    Locate {
        addr: EndpointAddr,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Signed {
    /// When it was signed (Unix ms), as its signer says.
    pub at: u64,
    pub by: EndpointId,
    pub change: Change,
    /// Hex ed25519 signature over the network, signer, time and change.
    pub sig: String,
}

impl Signed {
    pub fn new(network: &EndpointId, key: &SecretKey, at: u64, change: Change) -> Self {
        let by = key.public();
        let sig = wire::hex(&key.sign(&body(network, &by, at, &change)).to_bytes());
        Self { at, by, change, sig }
    }

    fn verifies(&self, network: &EndpointId) -> bool {
        let Some(Ok(bytes)) = wire::unhex(&self.sig).map(<[u8; Signature::LENGTH]>::try_from) else { return false };
        self.by.verify(&body(network, &self.by, self.at, &self.change), &Signature::from_bytes(&bytes)).is_ok()
    }
}

fn body(network: &EndpointId, by: &EndpointId, at: u64, change: &Change) -> Vec<u8> {
    serde_json::to_vec(&(network, by, at, change)).expect("a change always serializes")
}

/// The network as this computer knows it.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Roster {
    /// The network's id: its root key.
    pub network: EndpointId,
    log: BTreeSet<Signed>,
    #[serde(skip)]
    members: BTreeMap<EndpointId, Member>,
    #[serde(skip)]
    removed: BTreeSet<EndpointId>,
}

impl PartialEq for Roster {
    fn eq(&self, other: &Self) -> bool {
        self.network == other.network && self.log == other.log
    }
}

impl Roster {
    /// A new network with `me` as its owner. Returns it with the root key, which the caller
    /// shows once as the recovery code and keeps nowhere.
    pub fn create(me: &SecretKey, name: String, addr: EndpointAddr, at: u64) -> (Self, SecretKey) {
        let root = SecretKey::generate();
        let network = root.public();
        let mut roster = Self { network, log: BTreeSet::new(), members: BTreeMap::new(), removed: BTreeSet::new() };
        roster.log.insert(Signed::new(&network, &root, at, Change::Owner { id: me.public(), name }));
        roster.log.insert(Signed::new(&network, me, at, Change::Locate { addr }));
        roster.rebuild();
        (roster, root)
    }

    /// Signs `change` as `key` and adds it, if `key` may make it.
    pub fn sign(&mut self, key: &SecretKey, at: u64, change: Change) -> Result<()> {
        let entry = Signed::new(&self.network, key, at, change);
        let before = self.clone();
        self.log.insert(entry);
        self.rebuild();
        if self.members == before.members && self.removed == before.removed {
            *self = before;
            bail!("this computer isn't allowed to make that change");
        }
        Ok(())
    }

    pub fn members(&self) -> &BTreeMap<EndpointId, Member> {
        &self.members
    }

    pub fn is_member(&self, id: &EndpointId) -> bool {
        self.members.contains_key(id)
    }

    pub fn is_removed(&self, id: &EndpointId) -> bool {
        self.removed.contains(id)
    }

    pub fn role(&self, id: &EndpointId) -> Option<Role> {
        self.members.get(id).map(|m| m.role)
    }

    /// The member called `name`, or whose id starts with it.
    pub fn find(&self, name: &str) -> Option<EndpointId> {
        let name = name.trim();
        self.members
            .iter()
            .find(|(_, m)| m.name.eq_ignore_ascii_case(name))
            .or_else(|| self.members.iter().find(|(id, _)| name.len() >= 6 && id.to_string().starts_with(name)))
            .map(|(id, _)| *id)
    }

    pub fn name(&self, id: &EndpointId) -> String {
        self.members.get(id).map_or_else(|| id.fmt_short().to_string(), |m| m.name.clone())
    }

    /// `name`, or the first of `name-2`, `name-3`… no other computer has.
    pub fn free_name(&self, name: &str, for_id: &EndpointId) -> String {
        let taken = |n: &str| self.find(n).is_some_and(|id| id != *for_id);
        if !taken(name) {
            return name.into();
        }
        // One more number than there are members: one of them is free.
        (2..=self.members.len() + 2).map(|n| format!("{name}-{n}")).find(|n| !taken(n)).expect("a number is free")
    }

    /// Takes in another member's copy: the entries that verify. Returns whether anything changed.
    pub fn merge(&mut self, other: &Roster) -> bool {
        if other.network != self.network {
            return false;
        }
        let before = self.log.len();
        for entry in &other.log {
            if self.log.len() >= MAX_ENTRIES {
                break;
            }
            if !self.log.contains(entry) && entry.verifies(&self.network) {
                self.log.insert(entry.clone());
            }
        }
        if self.log.len() == before {
            return false;
        }
        self.rebuild();
        true
    }

    /// Works out the members from the log. Who may sign what depends only on entries from above
    /// (root, then owner, then admins), so the result doesn't depend on arrival order.
    fn rebuild(&mut self) {
        let root = self.network;
        let log: Vec<&Signed> = self.log.iter().collect();
        // Owners in turn, each from the time the root named it.
        let mut owners: Vec<(u64, EndpointId, String)> = log
            .iter()
            .filter(|s| s.by == root)
            .filter_map(|s| match &s.change {
                Change::Owner { id, name } => Some((s.at, *id, name.clone())),
                _ => None,
            })
            .collect();
        owners.sort();
        let owner_at = |at: u64| owners.iter().rev().find(|(from, ..)| *from <= at).map(|(_, id, _)| *id);
        let top = |by: &EndpointId, at: u64| *by == root || owner_at(at) == Some(*by);
        let owner = owners.last().map(|(_, id, _)| *id);

        // Removals by the top, then admins with the time span they could sign in.
        let removals = |may: &dyn Fn(&Signed, &EndpointId) -> bool| -> BTreeMap<EndpointId, (u64, bool)> {
            let mut out: BTreeMap<EndpointId, (u64, bool)> = BTreeMap::new();
            for s in &log {
                if let Change::Remove { id, cascade } = &s.change
                    && may(s, id)
                {
                    let e = out.entry(*id).or_insert((s.at, *cascade));
                    *e = (e.0.min(s.at), e.1 || *cascade);
                }
            }
            out
        };
        let top_removed = removals(&|s, id| top(&s.by, s.at) && (s.by == root || Some(*id) != owner_at(s.at)));
        let mut promoted: BTreeMap<EndpointId, u64> = BTreeMap::new();
        for s in &log {
            if let Change::Promote { id } = &s.change
                && top(&s.by, s.at)
            {
                let at = promoted.entry(*id).or_insert(s.at);
                *at = (*at).min(s.at);
            }
        }
        let signs_until = |id: &EndpointId, at: u64, from: u64, removed: &BTreeMap<EndpointId, (u64, bool)>| {
            from <= at && removed.get(id).is_none_or(|&(until, cascade)| !cascade && at < until)
        };
        let admin_at =
            |id: &EndpointId, at: u64| promoted.get(id).is_some_and(|&from| signs_until(id, at, from, &top_removed));
        let admin_removed =
            removals(&|s, id| admin_at(&s.by, s.at) && Some(*id) != owner_at(s.at) && !promoted.contains_key(id));
        let mut removed = top_removed.clone();
        for (id, r) in &admin_removed {
            removed.entry(*id).or_insert(*r);
        }
        // A cascade-removed owner voids what it signed as owner, too.
        let voided = |by: &EndpointId| removed.get(by).is_some_and(|&(_, cascade)| cascade);
        let may_admit = |s: &Signed| !voided(&s.by) && (top(&s.by, s.at) || admin_at(&s.by, s.at));

        let mut admitted: BTreeMap<EndpointId, String> = BTreeMap::new();
        for (_, id, name) in &owners {
            admitted.entry(*id).or_insert_with(|| name.clone());
        }
        for s in &log {
            if let Change::Admit { id, name } = &s.change
                && may_admit(s)
            {
                admitted.entry(*id).or_insert_with(|| name.clone());
            }
        }
        let mut addrs: BTreeMap<EndpointId, (u64, EndpointAddr)> = BTreeMap::new();
        for s in &log {
            if let Change::Locate { addr } = &s.change
                && addr.id == s.by
                && addrs.get(&s.by).is_none_or(|(at, _)| s.at > *at)
            {
                addrs.insert(s.by, (s.at, addr.clone()));
            }
        }
        self.removed = removed.keys().copied().collect();
        self.members = admitted
            .into_iter()
            .filter(|(id, _)| !self.removed.contains(id))
            .map(|(id, name)| {
                let role = if Some(id) == owner {
                    Role::Owner
                } else if admin_at(&id, u64::MAX) {
                    Role::Admin
                } else {
                    Role::Member
                };
                let addr = addrs.remove(&id).map_or_else(|| EndpointAddr::new(id), |(_, a)| a);
                (id, Member { name, role, addr })
            })
            .collect();
    }

    /// A copy that came from disk or another computer: only the entries that verify count.
    #[must_use]
    pub fn verified(mut self) -> Self {
        let network = self.network;
        self.log.retain(|s| s.verifies(&network));
        self.log = std::mem::take(&mut self.log).into_iter().take(MAX_ENTRIES).collect();
        self.rebuild();
        self
    }

    pub fn load(dir: &Path) -> Result<Option<Self>> {
        match std::fs::read(dir.join(FILE)) {
            Ok(bytes) => {
                let roster: Self = serde_json::from_slice(&bytes).context("network.json is damaged")?;
                Ok(Some(roster.verified()))
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(e).context("couldn't read network.json"),
        }
    }

    pub fn save(&self, dir: &Path) -> Result<()> {
        let tmp = dir.join(format!("{FILE}.tmp"));
        std::fs::write(&tmp, serde_json::to_vec_pretty(self)?)?;
        std::fs::rename(&tmp, dir.join(FILE)).context("couldn't save network.json")
    }
}

/// The recovery code for a root key, and back.
pub fn recovery_code(root: &SecretKey) -> String {
    let hex = wire::hex(&root.to_bytes());
    hex.as_bytes().chunks(8).map(|c| String::from_utf8_lossy(c).into_owned()).collect::<Vec<_>>().join("-")
}

pub fn root_from_code(code: &str) -> Result<SecretKey> {
    let hex: String = code.chars().filter(char::is_ascii_hexdigit).collect();
    let bytes: [u8; 32] = wire::unhex(&hex)
        .and_then(|b| b.try_into().ok())
        .ok_or_else(|| anyhow!("a recovery code is 64 hex characters"))?;
    Ok(SecretKey::from_bytes(&bytes))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key() -> SecretKey {
        SecretKey::generate()
    }

    fn addr(k: &SecretKey) -> EndpointAddr {
        EndpointAddr::new(k.public())
    }

    #[test]
    fn the_owner_admits_admins_admit_members_cannot() {
        let (desk, server, laptop, phone) = (key(), key(), key(), key());
        let (mut r, _root) = Roster::create(&desk, "desk".into(), addr(&desk), 1);
        assert_eq!(r.role(&desk.public()), Some(Role::Owner));
        r.sign(&desk, 2, Change::Admit { id: server.public(), name: "server".into() }).unwrap();
        r.sign(&desk, 3, Change::Promote { id: server.public() }).unwrap();
        r.sign(&server, 4, Change::Admit { id: laptop.public(), name: "laptop".into() }).unwrap();
        assert_eq!(r.role(&server.public()), Some(Role::Admin));
        assert_eq!(r.role(&laptop.public()), Some(Role::Member));
        // A plain member can neither admit nor remove.
        assert!(r.sign(&laptop, 5, Change::Admit { id: phone.public(), name: "phone".into() }).is_err());
        assert!(r.sign(&laptop, 5, Change::Remove { id: server.public(), cascade: false }).is_err());
        // An admin can't remove another admin or the owner, and can't promote.
        assert!(r.sign(&server, 6, Change::Remove { id: desk.public(), cascade: false }).is_err());
        assert!(r.sign(&server, 6, Change::Promote { id: laptop.public() }).is_err());
        r.sign(&server, 7, Change::Remove { id: laptop.public(), cascade: false }).unwrap();
        assert!(!r.is_member(&laptop.public()) && r.is_removed(&laptop.public()));
    }

    #[test]
    fn copies_converge_whatever_the_order() {
        let (desk, server, laptop) = (key(), key(), key());
        let (mut a, _root) = Roster::create(&desk, "desk".into(), addr(&desk), 1);
        a.sign(&desk, 2, Change::Admit { id: server.public(), name: "server".into() }).unwrap();
        let mut b = a.clone();
        a.sign(&desk, 3, Change::Promote { id: server.public() }).unwrap();
        // b hears of the promotion only after the admin's admission: once merged, both agree.
        let mut early = a.clone();
        early.sign(&server, 4, Change::Admit { id: laptop.public(), name: "laptop".into() }).unwrap();
        b.log.extend(early.log.iter().filter(|s| s.by == server.public()).cloned());
        b.rebuild();
        assert!(!b.is_member(&laptop.public()), "not yet: b doesn't know server is an admin");
        assert!(b.merge(&a));
        assert!(b.is_member(&laptop.public()));
        assert!(a.merge(&b));
        assert_eq!(a.members(), b.members());
        assert!(!a.merge(&b), "nothing new the second time");
    }

    #[test]
    fn forged_or_foreign_entries_are_dropped() {
        let (desk, mallory) = (key(), key());
        let (mut r, _root) = Roster::create(&desk, "desk".into(), addr(&desk), 1);
        let mut forged = r.clone();
        let mut entry = Signed::new(&r.network, &mallory, 2, Change::Admit { id: mallory.public(), name: "m".into() });
        entry.by = desk.public();
        forged.log.insert(entry);
        assert!(!r.merge(&forged));
        let (other, _) = Roster::create(&mallory, "m".into(), addr(&mallory), 1);
        assert!(!r.merge(&other));
        assert_eq!(r.members().len(), 1);
    }

    #[test]
    fn removing_a_stolen_admin_with_cascade_voids_its_admissions() {
        let (desk, server, laptop, evil) = (key(), key(), key(), key());
        let (mut r, _root) = Roster::create(&desk, "desk".into(), addr(&desk), 1);
        r.sign(&desk, 2, Change::Admit { id: server.public(), name: "server".into() }).unwrap();
        r.sign(&desk, 3, Change::Promote { id: server.public() }).unwrap();
        r.sign(&server, 4, Change::Admit { id: laptop.public(), name: "laptop".into() }).unwrap();
        r.sign(&server, 5, Change::Admit { id: evil.public(), name: "evil".into() }).unwrap();
        let mut retired = r.clone();
        retired.sign(&desk, 6, Change::Remove { id: server.public(), cascade: false }).unwrap();
        assert!(retired.is_member(&laptop.public()), "retiring an admin keeps whom it admitted");
        r.sign(&desk, 6, Change::Remove { id: server.public(), cascade: true }).unwrap();
        assert!(!r.is_member(&evil.public()) && !r.is_member(&laptop.public()));
    }

    #[test]
    fn the_recovery_code_moves_the_owner() {
        let (desk, laptop) = (key(), key());
        let (mut r, root) = Roster::create(&desk, "desk".into(), addr(&desk), 1);
        r.sign(&desk, 2, Change::Admit { id: laptop.public(), name: "laptop".into() }).unwrap();
        let code = recovery_code(&root);
        let root = root_from_code(&code).unwrap();
        r.sign(&root, 3, Change::Owner { id: laptop.public(), name: "laptop".into() }).unwrap();
        r.sign(&laptop, 4, Change::Remove { id: desk.public(), cascade: false }).unwrap();
        assert_eq!(r.role(&laptop.public()), Some(Role::Owner));
        assert!(!r.is_member(&desk.public()));
        assert!(root_from_code("nope").is_err());
    }

    #[test]
    fn taken_names_get_a_number() {
        let (desk, other) = (key(), key());
        let (r, _) = Roster::create(&desk, "laptop".into(), addr(&desk), 1);
        assert_eq!(r.free_name("laptop", &other.public()), "laptop-2");
        assert_eq!(r.free_name("laptop", &desk.public()), "laptop");
        assert_eq!(r.free_name("desk", &other.public()), "desk");
    }

    #[test]
    fn a_computer_moves_itself_only() {
        let (desk, laptop) = (key(), key());
        let (mut r, _) = Roster::create(&desk, "desk".into(), addr(&desk), 1);
        r.sign(&desk, 2, Change::Admit { id: laptop.public(), name: "laptop".into() }).unwrap();
        let moved = addr(&laptop).with_ip_addr("10.0.0.2:1".parse().unwrap());
        r.sign(&laptop, 3, Change::Locate { addr: moved.clone() }).unwrap();
        assert_eq!(r.members()[&laptop.public()].addr, moved);
        let fake = addr(&laptop).with_ip_addr("6.6.6.6:1".parse().unwrap());
        assert!(r.sign(&desk, 4, Change::Locate { addr: fake }).is_err());
    }
}
