//! The sealed-container (`.glc`) reader: grammar parse + envelope
//! verification, shared by the `glc-check` binary and the
//! [`crate::reprovocab::baked`] vocabulary derivation.
//!
//! A `.glc` file carries signed geolog commit envelopes (skeleton +
//! canonical body) in the pinned container grammar, preceded by a
//! prerequisite table naming the vocabulary revisions the commits'
//! external references resolve against. This reader is INDEPENDENT of
//! the producer's writer (mtk-glc): the grammar is the pinned contract
//! between them, and the refusal loci mirror the certified reader's
//! taxonomy. (Sharing between this library and its own `glc-check`
//! binary is deliberate; independence is from the producer, not from
//! ourselves.)

use geolog_envelope::body::{Body, Op};
use geolog_envelope::receipt::{store_body, BodyStore};
use geolog_envelope::{SignedEnvelope, Skeleton};

/// A body store that keeps nothing: container verification needs the
/// [`store_body`] receipt (the hash gate), not durability.
pub struct InertBodyStore;

impl BodyStore for InertBodyStore {
    type Error = std::convert::Infallible;
    fn store_durable(&mut self, _body_bytes: &[u8]) -> Result<(), Self::Error> {
        Ok(())
    }
}

/// One parsed prerequisite entry.
pub struct Prereq {
    pub flag: u8,
    pub chid: [u8; 32],
}

/// One parsed commit record: raw envelope halves.
pub struct CommitRec {
    pub sig: [u8; 64],
    pub skel: Vec<u8>,
    pub body: Vec<u8>,
}

/// A parsed (not yet verified) container.
pub struct Container {
    pub prereqs: Vec<Prereq>,
    pub commits: Vec<CommitRec>,
}

/// Minimum wire footprint of one prerequisite entry: 1 flag byte +
/// 32 chid bytes (the flag-1 roster id is optional extra). Used only
/// to bound a capacity hint — never as a grammar rule.
const PREREQ_MIN_WIRE: usize = 33;

/// Minimum wire footprint of one commit record: 4 (env_len) +
/// 64 (env_len ≥ 64 is enforced) + 4 (body_len) + 0 (empty body).
const COMMIT_MIN_WIRE: usize = 72;

/// Parse the pinned container grammar (magic, version, prerequisite
/// table order and flags, commit records, no trailing bytes).
pub fn parse_container(bytes: &[u8]) -> Result<Container, String> {
    let need = |n: usize, at: usize, what: &str| -> Result<(), String> {
        // Overflow-free extent check: compare `n` against the bytes
        // remaining past `at` (a sum `at + n` of a cursor with a
        // wire-derived length could wrap on 32-bit hosts).
        if n > bytes.len().saturating_sub(at) {
            Err(format!("{what}_truncated at {at}"))
        } else {
            Ok(())
        }
    };
    need(8, 0, "magic")?;
    if &bytes[0..8] != b"geologfl" {
        return Err("magic: not a geolog commit container".to_string());
    }
    need(4, 8, "version")?;
    let ver = u32::from_le_bytes(bytes[8..12].try_into().unwrap());
    if ver != 1 {
        return Err(format!(
            "container_version: {ver} unsupported (this reader: 1)"
        ));
    }
    need(4, 12, "prereq_count")?;
    let pcount = u32::from_le_bytes(bytes[12..16].try_into().unwrap()) as usize;
    let mut pos = 16usize;
    // Never allocate attacker-chosen capacity ahead of validation — a
    // 16-byte input could otherwise request ~2^32 elements. Cap the
    // hint by what the remaining input could possibly hold; an honest
    // count is unaffected (its records exist, so remaining/min-size ≥
    // count), while a lying count allocates at most O(input bytes)
    // before the first per-record `need` refuses.
    let mut prereqs =
        Vec::with_capacity(pcount.min(bytes.len().saturating_sub(pos) / PREREQ_MIN_WIRE));
    for _ in 0..pcount {
        need(1, pos, "prereq")?;
        let flag = bytes[pos];
        if flag == 3 {
            return Err(format!("prereq_flag_3_reserved at {pos}"));
        }
        if flag > 3 {
            return Err(format!("prereq_flag_unknown: {flag} at {pos}"));
        }
        need(33, pos, "prereq")?;
        let chid: [u8; 32] = bytes[pos + 1..pos + 33].try_into().unwrap();
        pos += 33;
        if flag == 1 {
            need(2, pos, "prereq_roster_id")?;
            pos += 2;
        }
        prereqs.push(Prereq { flag, chid });
    }
    for w in prereqs.windows(2) {
        if w[0].chid >= w[1].chid {
            return Err("prereq_order: chids not strictly ascending".to_string());
        }
    }
    need(4, pos, "commit_count")?;
    let ccount = u32::from_le_bytes(bytes[pos..pos + 4].try_into().unwrap()) as usize;
    pos += 4;
    if ccount == 0 {
        return Err("commit_count_zero".to_string());
    }
    // Same capacity guard as the prereq table above.
    let mut commits =
        Vec::with_capacity(ccount.min(bytes.len().saturating_sub(pos) / COMMIT_MIN_WIRE));
    for _ in 0..ccount {
        need(4, pos, "env_len")?;
        let env_len = u32::from_le_bytes(bytes[pos..pos + 4].try_into().unwrap()) as usize;
        pos += 4;
        if env_len < 64 {
            return Err(format!("env_len_under_signature: {env_len} at {pos}"));
        }
        need(env_len, pos, "envelope")?;
        let sig: [u8; 64] = bytes[pos..pos + 64].try_into().unwrap();
        let skel = bytes[pos + 64..pos + env_len].to_vec();
        pos += env_len;
        need(4, pos, "body_len")?;
        let body_len = u32::from_le_bytes(bytes[pos..pos + 4].try_into().unwrap()) as usize;
        pos += 4;
        need(body_len, pos, "body")?;
        let body = bytes[pos..pos + body_len].to_vec();
        pos += body_len;
        commits.push(CommitRec { sig, skel, body });
    }
    if pos != bytes.len() {
        return Err(format!(
            "trailing_bytes: {} after last commit",
            bytes.len() - pos
        ));
    }
    Ok(Container { prereqs, commits })
}

/// One verified commit: canonical ops + skeleton deps + own address.
pub struct VerifiedCommit {
    pub ops: Vec<Op>,
    pub deps: Vec<[u8; 32]>,
    pub own: [u8; 32],
}

/// Envelope verification shared by every checking mode: per commit —
/// skeleton decode, ed25519 signature over the skeleton bytes,
/// body-hash binding (the skeleton names exactly the attached body),
/// canonical body decode (one body, one byte string — the fixed-point
/// gate) — and dep discipline: every skeleton dep resolves against
/// `roster` or an earlier commit in the same container; unknown
/// references refuse loudly, never pass silently.
pub fn verify_commits(c: &Container, roster: &[[u8; 32]]) -> Result<Vec<VerifiedCommit>, String> {
    let mut seen_addrs: Vec<[u8; 32]> = Vec::new();
    let mut out = Vec::new();
    for (ci, rec) in c.commits.iter().enumerate() {
        let skel = Skeleton::decode(&rec.skel).map_err(|e| format!("commit {ci} skeleton: {e}"))?;
        let env = SignedEnvelope::from_raw_parts(skel, rec.sig);
        env.verify_signature()
            .map_err(|e| format!("commit {ci} signature: {e}"))?;
        let receipt = match store_body(&mut InertBodyStore, &rec.body) {
            Ok(r) => r,
            Err(e) => match e {},
        };
        env.verify_with_body(&receipt)
            .map_err(|e| format!("commit {ci} body_hash: {e}"))?;
        let body = Body::decode(&rec.body).map_err(|e| format!("commit {ci} body: {e}"))?;
        let own = env.commit_hash();
        let deps = env.skeleton().deps().to_vec();
        for d in &deps {
            if !roster.contains(d) && !seen_addrs.contains(d) {
                return Err(format!("commit {ci} dep_unresolved: {}", hex32(d)));
            }
        }
        seen_addrs.push(own);
        out.push(VerifiedCommit {
            ops: body.ops().to_vec(),
            deps,
            own,
        });
    }
    Ok(out)
}

/// Lowercase-hex spelling of a 32-byte chid.
pub fn hex32(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn header(pcount: u32) -> Vec<u8> {
        let mut v = Vec::new();
        v.extend_from_slice(b"geologfl");
        v.extend_from_slice(&1u32.to_le_bytes());
        v.extend_from_slice(&pcount.to_le_bytes());
        v
    }

    /// Refusal witness: a 16-byte input claiming ~2^32 prereqs must
    /// parse-error cheaply. Before the capacity guard, this very input
    /// requested a ~141 GB allocation (u32::MAX × 33-byte `Prereq`)
    /// before validating a single record — reverting the guard makes
    /// this test abort, which is its mutant value.
    #[test]
    fn huge_prereq_count_refuses_cheaply() {
        let bytes = header(u32::MAX);
        assert_eq!(bytes.len(), 16);
        let Err(err) = parse_container(&bytes) else {
            panic!("huge prereq count must refuse");
        };
        assert!(err.contains("prereq_truncated"), "got: {err}");
    }

    /// The commit-table twin: prereq table empty, commit count lies.
    #[test]
    fn huge_commit_count_refuses_cheaply() {
        let mut bytes = header(0);
        bytes.extend_from_slice(&u32::MAX.to_le_bytes()); // commit_count
        let Err(err) = parse_container(&bytes) else {
            panic!("huge commit count must refuse");
        };
        assert!(err.contains("env_len_truncated"), "got: {err}");
    }

    /// Extent-check overflow witness: `need` must not compute `at + n`
    /// unchecked — an env_len near usize::MAX (via u32::MAX on 32-bit
    /// hosts) must refuse as truncation, never wrap into acceptance.
    #[test]
    fn env_len_near_max_refuses_as_truncation() {
        let mut bytes = header(0);
        bytes.extend_from_slice(&1u32.to_le_bytes()); // commit_count = 1
        bytes.extend_from_slice(&u32::MAX.to_le_bytes()); // env_len
        let Err(err) = parse_container(&bytes) else {
            panic!("oversize env_len must refuse");
        };
        assert!(err.contains("envelope_truncated"), "got: {err}");
    }

    /// The guard is a capacity hint, not a grammar rule: an honest
    /// container whose counts match its records still parses, with the
    /// tables fully populated (capacity clamping never truncates).
    #[test]
    fn honest_counts_unaffected_by_capacity_guard() {
        let mut bytes = header(2);
        for b in [1u8, 2u8] {
            bytes.push(0); // flag 0: no roster id
            bytes.extend_from_slice(&[b; 32]); // chid, ascending
        }
        bytes.extend_from_slice(&1u32.to_le_bytes()); // commit_count = 1
        bytes.extend_from_slice(&64u32.to_le_bytes()); // env_len = 64 (sig only)
        bytes.extend_from_slice(&[0u8; 64]); // signature bytes
        bytes.extend_from_slice(&0u32.to_le_bytes()); // body_len = 0
        let c = parse_container(&bytes).expect("honest container parses");
        assert_eq!(c.prereqs.len(), 2);
        assert_eq!(c.commits.len(), 1);
        assert!(c.commits[0].skel.is_empty());
        assert!(c.commits[0].body.is_empty());
    }
}
