//! The baked-pair reproduction vocabulary, version 1 — the first
//! DERIVED vocabulary: its declaration index is computed from the
//! minted revisions' own decoded declaration rows (the meta-schema
//! loader's `DepView`), never transcribed.
//!
//! ## What is pinned, what is derived
//!
//! The PINS are the four commit chids below, byte-identical to
//! `theories/pins/baked_v1_pins.txt` (the [`tests`] assert the tie):
//! the two closure revisions minted from the qtsl-normative theory
//! bytes — **qc** = BernsteinLogic + Qtsl (the proof tower + the
//! omnibus), **dc** = qc + Dtmc — plus the two goldens every sealed
//! revision deps (genesis, ground-comparisons). Everything else —
//! sort and function names, counters, domains, codomains,
//! relational/side-condition flags — is DERIVED at load time from the
//! commit bodies through the engine's own meta-schema loader
//! (`load_revision`, full conformance, loud rejections) and its
//! cross-revision view (`revision_view` → `DepView`). Because the
//! chids are content addresses, the derivation input cannot drift
//! from the mint: bytes that decode differently would hash
//! differently and refuse at the pin gate.
//!
//! This is the successor [`super::fluid_v0`]'s module docs promised
//! ("moving these declarations onto staged theory commits, with the
//! index derived from decoded declaration rows"). Versioning: the
//! append-only store resolves every prior revision event's chids
//! forever, and reproduction lanes pin repository revisions, so an
//! already-vendored lane keeps building the provider it shipped with;
//! this module tracks the CURRENT revision event of the one uniform
//! schema all new emission targets (revision event 7, the timed-floor
//! mint: the TimedFloor fragment spliced whole into the omnibus —
//! hrpDropAtMost joins HRowPolarity, plus the TrMeter premise class,
//! the QPAlwaysTFromLineage / QPAlwaysTFromFold / QRateFromClock node
//! species with their walks and node-keyed mirror demands, the
//! lineage-offsets relation, and KSupportWarrant; the proof tower
//! file is BYTE-STABLE at this event — see
//! `theories/pins/baked_v1_pins.txt`'s header for the event's
//! contents; the [`tests`] assert the pin tie, so this prose can
//! never silently outrank the pins file).
//!
//! ## The pin roster (primary pair + retained legacy, per event)
//!
//! Revision events replace this module's PRIMARY constants and
//! embedded extracts IN PLACE at each mint swap. The default rule is
//! greenfield: backward compatibility is not yet a goal — committed
//! corpora re-emit at the current event via the re-conduct campaign,
//! the append-only STORE (not this checker) is where history lives,
//! and superseded extracts are deleted at the swap (git history
//! retains them). [`BAKED_ROSTER`] leads with the primary pair
//! ([`BAKED_QC_V1_REV`]/[`BAKED_DC_V1_REV`], tracking
//! `theories/pins/baked_v1_pins.txt` at [`BAKED_PRIMARY_EVENT`]) and
//! remains append-capable for the exceptional case where an
//! in-flight emission campaign still targets the outgoing pair — the
//! event-6 swap exercised that capability for the first time, and
//! the event-6.1 and event-7 swaps retain their outgoing generations
//! on the same ground (the retained rows carry their reasons in
//! place). Certificate-mode
//! dispatch resolves through [`resolve_baked_rev`]; chain-mode
//! containers derive from their OWN bytes and their pin gate
//! recognizes the primary pair only.
//!
//! ## The embedded chain
//!
//! `fixtures/baked/{qc,dc}-baked-<event>.glc` (suffixed by the HOUSE
//! event name — the suffix tracks the house revision-event name,
//! never the bare generation counter, which counts every swap
//! including fast-follows) are the production store's own extracts
//! (byte-identical across stores — the mint ceremony's
//! reproducibility receipt), each carrying the four commits of one
//! closure's chain: genesis, ground-comparisons, the revision, and
//! the seal companion (raw source + registry text). The checker
//! derives its certificate-mode vocabulary from these embedded bytes;
//! chain-mode containers are derived from their OWN bytes and only
//! the pins are consulted. Superseded events' extracts are DELETED at
//! the swap per the greenfield rule above, EXCEPT while a legacy
//! roster row still pins them (the event-6.1, event-6, and event-5.1
//! pairs below).

use crate::container::{parse_container, verify_commits, VerifiedCommit};
use crate::theory::{Chid, DomainSig, FunDecl, Ground, SortKey, TheoryIndex};
use geolog_meta_rows::load::{ExtDecl, ExtDomain, ExtSortKey};
use geolog_meta_rows::revhash::revision_hash;
use geolog_meta_rows::view::revision_view;
use geolog_meta_rows::{load_revision, DepView, LoadCtx, MetaIds};
use std::collections::BTreeMap;

// ── event-7 mint (the timed-floor mint — generation counter 9,
// house name revision event 7: the TimedFloor fragment spliced whole
// into theory Qtsl by the deterministic mint assembler. hrpDropAtMost
// joins HRowPolarity (the hrp_closed refusal gains its third
// disjunct — the one mutation-shaped edit, which moves the qc/dc
// chids), plus the TrMeter premise class, the QPAlwaysTFromLineage /
// QPAlwaysTFromFold / QRateFromClock node species with their walks
// and node-keyed mirror demands, the lineage-offsets relation, and
// KSupportWarrant. BernsteinLogic (the proof tower / external-checker
// boundary) is BYTE-STABLE at this event. Primary while
// BAKED_PRIMARY_EVENT == 9) ──────────────────────────────────────────

/// Event-7 revision chid of the baked **qc** closure
/// (BernsteinLogic + Qtsl).
pub const BAKED_QC_E7_REV: [u8; 32] = [
    0x99, 0x52, 0x50, 0x6d, 0xd2, 0x49, 0x1e, 0x88, 0x0a, 0x61, 0x07, 0x47, 0x1a, 0x1c, 0xa9, 0x2f,
    0x66, 0xa4, 0xa3, 0x3a, 0x64, 0xa8, 0xcc, 0x25, 0x08, 0x33, 0xd0, 0x04, 0x02, 0xe3, 0xb0, 0xe6,
];
/// Event-7 revision chid of the baked **dc** closure (qc + Dtmc).
pub const BAKED_DC_E7_REV: [u8; 32] = [
    0xbc, 0x30, 0xa5, 0xf3, 0xb2, 0x2d, 0xa4, 0x87, 0xf7, 0x70, 0x80, 0xd5, 0xaa, 0x41, 0x86, 0x08,
    0x43, 0x76, 0x55, 0x2b, 0x7c, 0xe0, 0x70, 0xcc, 0xf4, 0x4d, 0x4c, 0x52, 0x26, 0xc5, 0xaa, 0x96,
];

/// The event-7 qc chain container (the production store's extract).
pub fn qc_e7_container_bytes() -> &'static [u8] {
    include_bytes!("../../fixtures/baked/qc-baked-e7.glc")
}

/// The event-7 dc chain container.
pub fn dc_e7_container_bytes() -> &'static [u8] {
    include_bytes!("../../fixtures/baked/dc-baked-e7.glc")
}

// ── event-6.1 mint (the modal-scoping re-mode — generation counter
// 8, house name revision event 6.1: the fast-follow that re-moded
// every side-condition demand mint chase → report across the proof
// tower, the omnibus, and the species files, per the engine's
// modal-scoping lint (a side-condition's extension is decided by its
// evaluator, never asserted by derivation). Vocabulary is unchanged
// from event 6 declaration-for-declaration; only axiom modes — and
// hence the sealed revision bytes — move. LEGACY since the event-7
// swap; retained while emission campaigns minted against this pair
// are still in flight — see the roster comment below) ───────────────

/// Event-6.1 revision chid of the baked **qc** closure
/// (BernsteinLogic + Qtsl).
pub const BAKED_QC_E6P1_REV: [u8; 32] = [
    0x64, 0x19, 0xae, 0x4b, 0xe3, 0xde, 0x7b, 0x25, 0x0d, 0x6e, 0x5b, 0xe4, 0x72, 0xcf, 0x8a, 0x55,
    0xd8, 0x75, 0xe2, 0x1a, 0x95, 0x09, 0xee, 0x1f, 0x66, 0xe3, 0xd0, 0x07, 0x92, 0xa8, 0xec, 0x53,
];
/// Event-6.1 revision chid of the baked **dc** closure (qc + Dtmc).
pub const BAKED_DC_E6P1_REV: [u8; 32] = [
    0x6d, 0x8a, 0x41, 0x8f, 0xe5, 0xc0, 0x19, 0xe0, 0x87, 0xe1, 0xb8, 0x62, 0x5b, 0x41, 0xa4, 0x7f,
    0x6f, 0xd9, 0x0c, 0xea, 0xa4, 0x5c, 0x3d, 0x54, 0xc7, 0xde, 0x62, 0xea, 0x3f, 0xd5, 0xed, 0xd7,
];

/// The event-6.1 qc chain container (the production store's extract).
pub fn qc_e6p1_container_bytes() -> &'static [u8] {
    include_bytes!("../../fixtures/baked/qc-baked-e6p1.glc")
}

/// The event-6.1 dc chain container.
pub fn dc_e6p1_container_bytes() -> &'static [u8] {
    include_bytes!("../../fixtures/baked/dc-baked-e6p1.glc")
}

// ── event-6 mint (the six-passenger coordinated event: the
// event-rate envelope atoms, the distance judgments, the timed core,
// the discharge kit, the verdict-stratum re-cut onto face-typed
// forms with the unified QForallSat warrant seam, and the
// lower-bound renames — the provider's generation counter says 7,
// the house name is revision event 6: the counter counts every swap
// including the 5.1 fast-follow, so counter and house name differ by
// one from event 5.1 onward. LEGACY since the event-6.1 swap;
// retained while emission campaigns minted against this pair are
// still in flight — see the roster comment below) ────────────────────

/// Event-6 revision chid of the baked **qc** closure
/// (BernsteinLogic + Qtsl).
pub const BAKED_QC_E6_REV: [u8; 32] = [
    0xac, 0x5f, 0xdd, 0x9c, 0xd9, 0x14, 0x8c, 0xef, 0xe6, 0xe0, 0x0e, 0xe6, 0x55, 0x1f, 0x9b, 0x27,
    0x6d, 0xcd, 0xb5, 0x7e, 0x3d, 0xb4, 0x4b, 0xd9, 0x25, 0x3d, 0x16, 0xe3, 0x48, 0x51, 0x57, 0x33,
];
/// Event-6 revision chid of the baked **dc** closure (qc + Dtmc).
pub const BAKED_DC_E6_REV: [u8; 32] = [
    0x44, 0xb8, 0xcf, 0x8c, 0x2a, 0xae, 0xae, 0x80, 0xc8, 0x01, 0x10, 0x3c, 0xb0, 0x69, 0xc5, 0xa6,
    0x07, 0x55, 0x76, 0xdb, 0xc7, 0x8c, 0x5d, 0xed, 0xc5, 0x2f, 0x15, 0x91, 0x3a, 0x3e, 0x79, 0x11,
];

/// The event-6 qc chain container (the production store's extract).
pub fn qc_e6_container_bytes() -> &'static [u8] {
    include_bytes!("../../fixtures/baked/qc-baked-e6.glc")
}

/// The event-6 dc chain container.
pub fn dc_e6_container_bytes() -> &'static [u8] {
    include_bytes!("../../fixtures/baked/dc-baked-e6.glc")
}

// ── event-5.1 mint (the transport lift — generation counter 6, house
// name revision event 5.1: the fast-follow that completed event-5's
// critical path by widening the H-CONTRACT admission from sum-only to
// sum + hagConjPow. LEGACY since the event-6 swap; retained while the
// in-flight emission sweep pinned to this pair completes — see the
// roster comment below) ──────────────────────────────────────────────

/// Event-5.1 revision chid of the baked **qc** closure
/// (BernsteinLogic + Qtsl).
pub const BAKED_QC_E5P1_REV: [u8; 32] = [
    0x68, 0x62, 0xed, 0xc8, 0x8f, 0xf1, 0xd7, 0x88, 0x55, 0x0d, 0x19, 0x60, 0x78, 0xa2, 0x8c, 0xb2,
    0xfe, 0x97, 0x1f, 0x10, 0xd4, 0x78, 0xa5, 0xe3, 0x28, 0x00, 0xf2, 0x89, 0x2a, 0x72, 0x92, 0xb9,
];
/// Event-5.1 revision chid of the baked **dc** closure (qc + Dtmc).
pub const BAKED_DC_E5P1_REV: [u8; 32] = [
    0xb3, 0x90, 0x07, 0x9a, 0x06, 0x3f, 0x05, 0xbb, 0x3f, 0x34, 0x2e, 0x60, 0x42, 0x4a, 0x88, 0x4f,
    0xc3, 0x49, 0x7a, 0x02, 0x25, 0xde, 0xd1, 0xbf, 0x21, 0x51, 0xb4, 0x13, 0x9e, 0xcd, 0x84, 0x38,
];

/// The event-5.1 qc chain container (the production store's extract).
pub fn qc_e5p1_container_bytes() -> &'static [u8] {
    include_bytes!("../../fixtures/baked/qc-baked-e5p1.glc")
}

/// The event-5.1 dc chain container.
pub fn dc_e5p1_container_bytes() -> &'static [u8] {
    include_bytes!("../../fixtures/baked/dc-baked-e5p1.glc")
}

// ── the PRIMARY pair: tracks theories/pins/baked_v1_pins.txt ─────────
// The mint-swap point: a new revision event re-aims exactly these four
// aliases (+ BAKED_PRIMARY_EVENT + the legacy roster append below);
// every caller of the V1 names follows automatically, and the
// [`tests`] pins-file tie refuses a half-done swap.

/// The revision event the primary pair tracks (the pins file's
/// header). Exemption rosters and swap integrity key off this.
/// (Generation counter, not the house event name: 9 = house revision
/// event 7 — the counter counts every swap, fast-follows (5.1, 6.1)
/// included.)
pub const BAKED_PRIMARY_EVENT: u32 = 9;

/// Revision chid of the PRIMARY baked **qc** closure
/// (BernsteinLogic + Qtsl) — byte-identical to the pins file.
pub const BAKED_QC_V1_REV: [u8; 32] = BAKED_QC_E7_REV;
/// Revision chid of the PRIMARY baked **dc** closure (qc + Dtmc).
pub const BAKED_DC_V1_REV: [u8; 32] = BAKED_DC_E7_REV;
/// Commit chid of the genesis golden (every sealed revision's first
/// dep).
pub const BAKED_GENESIS_CHID: [u8; 32] = [
    0x6d, 0x96, 0x91, 0xe1, 0xd2, 0xee, 0x85, 0x8c, 0xd5, 0x00, 0x4d, 0x82, 0xdd, 0x6d, 0x6e, 0x78,
    0xd2, 0xb0, 0x22, 0x52, 0x63, 0x1c, 0x25, 0x1a, 0xd9, 0x92, 0xf8, 0x05, 0xac, 0x16, 0x9d, 0x94,
];
/// Commit chid of the ground-comparisons golden (the builtin
/// side-condition roster; every sealed revision's second dep).
pub const BAKED_COMPARISONS_CHID: [u8; 32] = [
    0xe9, 0x1b, 0xa7, 0xcd, 0x51, 0x1a, 0x3d, 0xb3, 0xe9, 0xf7, 0xbb, 0x36, 0xee, 0xdc, 0x3a, 0x73,
    0x18, 0xd5, 0x64, 0xd5, 0x7f, 0xf0, 0x18, 0x96, 0x5f, 0x11, 0x4e, 0x2d, 0x9d, 0xae, 0x25, 0x09,
];

/// The PRIMARY qc chain container.
pub fn qc_v1_container_bytes() -> &'static [u8] {
    qc_e7_container_bytes()
}

/// The PRIMARY dc chain container.
pub fn dc_v1_container_bytes() -> &'static [u8] {
    dc_e7_container_bytes()
}

// ── the roster: primary pair + legacy generations ────────────────────

/// One pinned baked-vocabulary generation entry: a closure revision of
/// one mint event, with its embedded chain extract. The roster row a
/// certificate's prereq pin resolves to.
#[derive(Clone, Copy)]
pub struct BakedPin {
    /// The revision event that minted this closure.
    pub event: u32,
    /// `"qc"` or `"dc"` (verdict-line vocabulary).
    pub closure: &'static str,
    /// The pinned revision chid.
    pub rev: [u8; 32],
    /// The embedded chain extract carrying this revision's chain.
    pub container: fn() -> &'static [u8],
}

impl BakedPin {
    /// Whether this row is the current primary pair's.
    pub fn is_primary(&self) -> bool {
        self.event == BAKED_PRIMARY_EVENT
    }
}

/// Every baked generation the checker recognizes, primary pair FIRST,
/// then legacy generations in reverse event order. Append-only below
/// the primary rows: a mint swap re-aims the primary aliases and
/// appends the outgoing pair here; entries are never removed
/// (certificate containers in the wild dep their mint's chids
/// forever, and the append-only store keeps resolving them — this
/// roster is the checker-side face of that promise).
pub const BAKED_ROSTER: &[BakedPin] = &[
    BakedPin {
        event: BAKED_PRIMARY_EVENT,
        closure: "qc",
        rev: BAKED_QC_V1_REV,
        container: qc_v1_container_bytes,
    },
    BakedPin {
        event: BAKED_PRIMARY_EVENT,
        closure: "dc",
        rev: BAKED_DC_V1_REV,
        container: dc_v1_container_bytes,
    },
    // LEGACY: the event-6.1 pair, retained at the event-7 swap.
    // Reason: the event-7 mint landed mid-campaign (hours after the
    // 6.1 fast-follow, on the same night's coordinated emission
    // work); campaigns minted against the 6.1 pair had not been
    // verified landed at this swap, so their containers must keep
    // checking until they re-conduct at the new primary. Drop these
    // rows, the e6p1 constants/extracts, and this comment together
    // once those campaigns land.
    BakedPin {
        event: 8,
        closure: "qc",
        rev: BAKED_QC_E6P1_REV,
        container: qc_e6p1_container_bytes,
    },
    BakedPin {
        event: 8,
        closure: "dc",
        rev: BAKED_DC_E6P1_REV,
        container: dc_e6p1_container_bytes,
    },
    // LEGACY: the event-6 pair, retained at the event-6.1 swap.
    // Reason: coordinated emission campaigns minted against the
    // event-6 pair were mid-flight at this swap (the re-mode landed
    // as a lint-forced fast-follow, not on a campaign boundary);
    // their containers must keep checking until they re-conduct at
    // the new primary. Drop these rows, the e6 constants/extracts,
    // and this comment together once those campaigns land.
    BakedPin {
        event: 7,
        closure: "qc",
        rev: BAKED_QC_E6_REV,
        container: qc_e6_container_bytes,
    },
    BakedPin {
        event: 7,
        closure: "dc",
        rev: BAKED_DC_E6_REV,
        container: dc_e6_container_bytes,
    },
    // LEGACY: the event-5.1 pair, retained DELIBERATELY at the
    // event-6 swap — the first exercise of this roster's append
    // capability, a conscious deviation from the greenfield
    // delete-at-swap default. Reason: a days-scale certificate-
    // emission sweep minted against the event-5.1 pair is still in
    // flight; its containers must keep checking until they
    // re-conduct at the new primary. Its drop condition (that sweep
    // landing) had not been verified met at the event-6.1 swap, so
    // the rows ride one more generation (drop them, the e5p1
    // constants/extracts, and the retention EXCEPT clause in the
    // module docs together once it is).
    BakedPin {
        event: 6,
        closure: "qc",
        rev: BAKED_QC_E5P1_REV,
        container: qc_e5p1_container_bytes,
    },
    BakedPin {
        event: 6,
        closure: "dc",
        rev: BAKED_DC_E5P1_REV,
        container: dc_e5p1_container_bytes,
    },
];

/// Resolve a revision chid against a roster (primary rows lead, so a
/// duplicated rev — which a lawful roster never carries — would
/// resolve primary). Factored from [`resolve_baked_rev`] so the
/// dispatch logic is testable against synthetic rosters.
pub fn resolve_rev_in<'a>(roster: &'a [BakedPin], rev: &[u8; 32]) -> Option<&'a BakedPin> {
    roster.iter().find(|p| p.rev == *rev)
}

/// Resolve a certificate's pinned revision chid against the primary
/// pair + legacy roster.
pub fn resolve_baked_rev(rev: &[u8; 32]) -> Option<&'static BakedPin> {
    resolve_rev_in(BAKED_ROSTER, rev)
}

/// Derivation statistics (the chain-mode verdict line's cargo, and the
/// honest record of what was skipped).
#[derive(Debug, Clone, Default)]
pub struct BakedStats {
    pub theories: usize,
    pub sorts: usize,
    pub funs: usize,
    pub fields: usize,
    /// Instance elements in the view (referencable objects) — carried
    /// as a count; they declare no vocabulary.
    pub objects: usize,
}

/// One derived vocabulary: the pinned revision, its index, and the
/// claim roster (every side-condition relation the revision declares,
/// name-sorted — the set of relations a certificate in this
/// vocabulary may lawfully claim).
#[derive(Debug, Clone)]
pub struct BakedVocab {
    pub revision: [u8; 32],
    pub index: TheoryIndex,
    pub claims: Vec<String>,
    pub stats: BakedStats,
}

fn find_commit<'a>(
    commits: &'a [VerifiedCommit],
    chid: [u8; 32],
    what: &str,
) -> Result<&'a VerifiedCommit, String> {
    commits
        .iter()
        .find(|c| c.own == chid)
        .ok_or_else(|| format!("chain_missing_{what}: no commit at the pinned chid"))
}

/// Map a cross-revision sort key into the provider's sort grammar.
/// Unrepresentable keys REFUSE (never a silent narrowing): a
/// declaration this mapping cannot carry would otherwise become a row
/// class the checker silently treats as unadjudicable content.
fn sort_key(k: &ExtSortKey, at: &str) -> Result<SortKey, String> {
    match k {
        ExtSortKey::Primordial(code) => Ground::from_dtype_code(*code)
            .map(SortKey::Ground)
            .ok_or_else(|| {
                format!("{at}: primordial dtype 0x{code:02x} outside the provider's ground roster")
            }),
        ExtSortKey::Decl(commit, counter) => Ok(SortKey::Elem((*commit, *counter))),
        ExtSortKey::DynTensor(code) => Ground::from_dtype_code(*code)
            .map(SortKey::TensorOf)
            .ok_or_else(|| {
                format!("{at}: tensor element dtype 0x{code:02x} outside the provider's roster")
            }),
        ExtSortKey::Meta(ms) => Err(format!(
            "{at}: meta-schema sort {ms:?} in a declaration signature — outside the \
             provider's sort grammar"
        )),
        ExtSortKey::List(code) => Err(format!(
            "{at}: List former over dtype 0x{code:02x} — the provider's sort grammar \
             has no List member (a certificate row citing it would be unadjudicable)"
        )),
    }
}

/// Build a [`TheoryIndex`] from one revision's [`DepView`]: sorts and
/// functions by their OWN counters (the chids certificates cite),
/// record domains resolved through the view's field declarations.
/// Duplicate names refuse — the provider's vocabulary builders resolve
/// by name, and a silently shadowed declaration would corrupt
/// resolution without a trace.
fn index_of_view(view: &DepView) -> Result<(TheoryIndex, BakedStats), String> {
    let mut ix = TheoryIndex::new(view.commit);
    let mut stats = BakedStats::default();
    // Counter order: deterministic construction, and `funs` in
    // canonical element order.
    let decls: BTreeMap<u32, &ExtDecl> = view.decls.iter().map(|(c, d)| (*c, d)).collect();
    for (&counter, decl) in &decls {
        match decl {
            ExtDecl::Theory { .. } => stats.theories += 1,
            ExtDecl::Object { .. } => stats.objects += 1,
            ExtDecl::Field { .. } => stats.fields += 1,
            ExtDecl::Sort { name, .. } => {
                if ix.sort(name).is_some() {
                    return Err(format!(
                        "duplicate sort name `{name}` in the revision — name resolution \
                         would silently shadow, refusing"
                    ));
                }
                ix.insert_sort(name, counter);
                stats.sorts += 1;
            }
            ExtDecl::Fun {
                name,
                relational,
                side_condition,
                domain,
                codomain,
                ..
            } => {
                if ix.fun(name).is_some() {
                    return Err(format!(
                        "duplicate fun name `{name}` in the revision — name resolution \
                         would silently shadow, refusing"
                    ));
                }
                let dom = match domain {
                    ExtDomain::Nullary => DomainSig::Nullary,
                    ExtDomain::Unary(k) => DomainSig::Unary(sort_key(k, name)?),
                    ExtDomain::Record(field_counters) => {
                        let mut fields = Vec::with_capacity(field_counters.len());
                        for fc in field_counters {
                            let Some(ExtDecl::Field {
                                name: fname,
                                fun,
                                sort,
                            }) = view.decls.get(fc)
                            else {
                                return Err(format!(
                                    "`{name}`: record field counter {fc} does not resolve \
                                     to a field declaration in the view"
                                ));
                            };
                            if *fun != counter {
                                return Err(format!(
                                    "`{name}`: field `{fname}` (counter {fc}) belongs to \
                                     fun counter {fun}, not this fun ({counter})"
                                ));
                            }
                            fields
                                .push((fname.clone(), sort_key(sort, &format!("{name}/{fname}"))?));
                        }
                        DomainSig::Record(fields)
                    }
                };
                let cod = match codomain {
                    Some(k) => Some(sort_key(k, &format!("{name} codomain"))?),
                    None => None,
                };
                ix.insert_fun(FunDecl {
                    name: name.clone(),
                    chid: (view.commit, counter),
                    relational: *relational,
                    side_condition: *side_condition,
                    domain: dom,
                    codomain: cod,
                });
                stats.funs += 1;
            }
        }
    }
    Ok((ix, stats))
}

/// Derive the vocabulary of the pinned revision `rev_pin` from a
/// verified commit set carrying its chain (genesis +
/// ground-comparisons + the revision; a seal companion may ride along
/// and is not consulted). The revision body is loaded under FULL
/// meta-schema conformance — a loud rejection list on any violation —
/// with the two goldens' views seated at the dep positions the
/// revision's own chid table assigns them.
pub fn derive_baked_vocab(
    rev_pin: [u8; 32],
    commits: &[VerifiedCommit],
) -> Result<BakedVocab, String> {
    // Genesis: the meta-schema bootstrap.
    let g = find_commit(commits, BAKED_GENESIS_CHID, "genesis")?;
    if !g.deps.is_empty() {
        return Err("genesis commit carries deps — not the golden".to_string());
    }
    let g_ctx = LoadCtx::genesis(&g.ops).map_err(|e| format!("genesis bootstrap: {e}"))?;
    let g_ir = load_revision(&g.ops, &g_ctx).map_err(|e| format!("genesis load: {e}"))?;
    let g_rh = revision_hash(&g_ir, &g_ctx).map_err(|e| format!("genesis hash: {e}"))?;
    let g_view = revision_view(&g_ir, &g_ctx, g.own, &g_rh);
    let meta = MetaIds::from_genesis_view(&g_view);

    // Ground-comparisons: the builtin side-condition roster, loaded
    // with genesis as its one dep.
    let sc = find_commit(commits, BAKED_COMPARISONS_CHID, "ground_comparisons")?;
    if sc.deps != [BAKED_GENESIS_CHID] {
        return Err("ground-comparisons commit's dep table is not [genesis]".to_string());
    }
    let sc_ctx = LoadCtx::with_deps(vec![g_view.clone()], meta.clone());
    let sc_ir =
        load_revision(&sc.ops, &sc_ctx).map_err(|e| format!("ground-comparisons load: {e}"))?;
    let sc_rh =
        revision_hash(&sc_ir, &sc_ctx).map_err(|e| format!("ground-comparisons hash: {e}"))?;
    let sc_view = revision_view(&sc_ir, &sc_ctx, sc.own, &sc_rh);

    // The revision itself, its golden views seated at the positions
    // its own (byte-sorted) chid table assigns.
    let rev = find_commit(commits, rev_pin, "revision")?;
    let views: Vec<DepView> = rev
        .deps
        .iter()
        .map(|d| {
            if *d == BAKED_GENESIS_CHID {
                Ok(g_view.clone())
            } else if *d == BAKED_COMPARISONS_CHID {
                Ok(sc_view.clone())
            } else {
                Err(format!(
                    "revision dep {} is neither golden — not a sealed-revision chain",
                    crate::container::hex32(d)
                ))
            }
        })
        .collect::<Result<_, String>>()?;
    if views.len() != 2 {
        return Err(format!(
            "revision dep table carries {} entries; a sealed revision deps exactly \
             [genesis, ground-comparisons]",
            views.len()
        ));
    }
    let ctx = LoadCtx::with_deps(views, meta);
    let ir = load_revision(&rev.ops, &ctx).map_err(|e| format!("revision load: {e}"))?;
    let rh = revision_hash(&ir, &ctx).map_err(|e| format!("revision hash: {e}"))?;
    let view = revision_view(&ir, &ctx, rev.own, &rh);

    let (index, stats) = index_of_view(&view)?;
    let mut claims: Vec<String> = index
        .funs
        .iter()
        .filter(|f| f.relational && f.side_condition)
        .map(|f| f.name.clone())
        .collect();
    claims.sort();
    Ok(BakedVocab {
        revision: rev.own,
        index,
        claims,
        stats,
    })
}

/// Parse + verify a chain container and derive the vocabulary of the
/// pinned revision it must carry. The container's commits resolve
/// against each other (extracts are self-contained and
/// dependency-ordered); nothing outside the pins is trusted.
pub fn baked_vocab_from_container(bytes: &[u8], rev_pin: [u8; 32]) -> Result<BakedVocab, String> {
    let c = parse_container(bytes)?;
    let commits = verify_commits(&c, &[])?;
    derive_baked_vocab(rev_pin, &commits)
}

/// The chid a claim row cites for a claim relation, resolved from the
/// derived index (claim name → (revision, counter)).
pub fn claim_chid(vocab: &BakedVocab, name: &str) -> Option<Chid> {
    vocab.index.fun(name).map(|d| d.chid)
}

/// Locate a chain container's sealed revision STRUCTURALLY: verify
/// the envelopes self-contained, then find the sole commit whose dep
/// table is exactly the two goldens (genesis + ground-comparisons).
/// Zero such commits = not a sealed-closure chain; two or more =
/// ambiguous — both refuse. This is the ONE definition of "the
/// revision of a chain": every consumer (the checker's staged lane,
/// the certificate emitter, test batteries) resolves through it, so
/// producer and checker cannot disagree about which revision a chain
/// carries. Returns the verified commits beside the revision so
/// callers need not re-verify.
pub fn staged_revision_of_chain(bytes: &[u8]) -> Result<([u8; 32], Vec<VerifiedCommit>), String> {
    let c = parse_container(bytes)?;
    let commits = verify_commits(&c, &[])?;
    let mut want = [BAKED_GENESIS_CHID, BAKED_COMPARISONS_CHID];
    want.sort_unstable();
    let mut rev: Option<[u8; 32]> = None;
    for vc in &commits {
        let mut deps = vc.deps.clone();
        deps.sort_unstable();
        if deps == want {
            if rev.replace(vc.own).is_some() {
                return Err("staged_chain_ambiguous: two sealed revisions in one chain \
                     container — a staged closure is one revision"
                    .to_string());
            }
        }
    }
    match rev {
        Some(r) => Ok((r, commits)),
        None => Err("staged_chain_unsealed: no commit deps exactly [genesis, \
             ground-comparisons] — not a sealed-closure chain this library \
             recognizes"
            .to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use geolog_meta_rows::load::{ExtOwner, MetaSort};

    fn fun(name: &str) -> ExtDecl {
        ExtDecl::Fun {
            name: name.to_string(),
            owner: ExtOwner::Meta,
            relational: true,
            side_condition: true,
            domain: ExtDomain::Nullary,
            codomain: None,
        }
    }

    /// Duplicate names refuse: the provider's builders resolve by name,
    /// and a silently shadowed declaration would corrupt resolution
    /// without a trace. (The minted closures carry no duplicates —
    /// this class is only reachable synthetically, so it is pinned
    /// here rather than through a fixture.)
    #[test]
    fn duplicate_fun_name_refuses() {
        let mut decls = std::collections::HashMap::new();
        decls.insert(1, fun("twice"));
        decls.insert(2, fun("twice"));
        let view = DepView {
            commit: [9u8; 32],
            revision_hash: [0u8; 32],
            decls,
        };
        let err = index_of_view(&view).expect_err("duplicate name refuses");
        assert!(err.contains("duplicate fun name `twice`"), "{err}");
    }

    /// Unrepresentable sort keys refuse rather than silently narrowing
    /// the index (a skipped declaration would become a row class the
    /// checker treats as unadjudicable content).
    #[test]
    fn meta_sort_key_refuses() {
        let mut decls = std::collections::HashMap::new();
        decls.insert(
            1,
            ExtDecl::Fun {
                name: "metaish".to_string(),
                owner: ExtOwner::Meta,
                relational: false,
                side_condition: false,
                domain: ExtDomain::Unary(ExtSortKey::Meta(MetaSort::Axiom)),
                codomain: None,
            },
        );
        let view = DepView {
            commit: [9u8; 32],
            revision_hash: [0u8; 32],
            decls,
        };
        let err = index_of_view(&view).expect_err("meta sort key refuses");
        assert!(err.contains("meta-schema sort"), "{err}");
    }
}
