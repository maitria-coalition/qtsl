//! glc-check — verify sealed certificate containers (`.glc`) on the
//! geolog fast path.
//!
//! A `.glc` file carries signed geolog commit envelopes (skeleton +
//! canonical body) in the pinned container grammar, preceded by a
//! prerequisite table naming the vocabulary revisions the commits'
//! external references resolve against. This checker:
//!
//! 1. **container + envelope integrity** — grammar (magic, version,
//!    prerequisite table order and flags, commit records, no trailing
//!    bytes), then per commit: skeleton decode, ed25519 signature
//!    over the skeleton bytes, body-hash binding (the skeleton names
//!    exactly the attached body), canonical body decode (one body,
//!    one byte string — the fixed-point gate);
//! 2. **reference discipline** — every prerequisite chid and every
//!    skeleton dep resolves against the pinned vocabulary roster (or
//!    an earlier commit in the same container); unknown references
//!    refuse loudly, never pass silently;
//! 3. **obligation discharge** — re-evaluated by the exact-rational
//!    ground provider over the decoded rows (the same plugin seam the
//!    engine's chase drives). A refusal is never a verdict; any
//!    non-holding obligation fails the file.
//!
//! Three pinned vocabularies, dispatched by the prerequisite table:
//!
//! - **fluid v0** (`reprovocab::fluid_v0`, synthetic revision): the
//!   certificate CLAIMS its side conditions as relation-instance rows;
//!   every claim row of a declared side-condition relation is
//!   discharged (the F2 fluid-drift lane).
//! - **BL v0** (`reprovocab::bl`, staged BLstack/BLCert revision
//!   pins): the certificate is a proof-object row set, and the checker
//!   ENUMERATES the APPLICATIVE obligations from the rule nodes
//!   itself — per PBernCone node one
//!   `allForwardDiffBernCoeffsSatisfyP` coefficient sweep (everything
//!   recomputed from simplex, S, degree, polynomial, predicate); per
//!   PFarkas node one `farkasCombinationValid` (coefficients,
//!   conclusion, and the node's own premise via Proof/concludes →
//!   Judgment/pre); per PSyzygy node `syzygyCombinationValid` AND
//!   `syzygyConclusionFormRel` (the conclusion met against the node's
//!   own judgment post — the tie that kills a self-consistent
//!   (λ, conclusion) co-forgery); per PEnclosure node one
//!   `enclosureWitnessValid` on the concluded EncJudgment; per
//!   PPromise node the two wire obligations
//!   (`promiseContractConfined`, `promiseWiresSeparated`). Nothing is
//!   trusted from the certificate, including any claim it might
//!   carry (the F3 supermartingale lane, widened by the F6 lean-route
//!   lane; bodies stay byte-identical to the committed reference
//!   listings).
//! - **SPDE moment v0** (`reprovocab::spde_v0`): claim rows in three
//!   relations (`spdeClaimValid` / `spdeTierWitnessValid` /
//!   `spdeSummedFloorValid`) discharged like the fluid lane's, with
//!   rates, mode floors, the covariance trace, and every exponential
//!   bracket recomputed from the sealed spectrum — derived
//!   quantities are never stored (the F5 stochastic-heat/Burgers
//!   moment lane).
//! - **Petri P-invariant v0** (`reprovocab::petri_v0`): the
//!   certificate carries PRIMARY DATA ONLY — one net (dimensions,
//!   sparse flow and marking rows) and its proposed invariant vectors
//!   (sparse coefficients, stated initial charges). The checker
//!   CONSTRUCTS every obligation itself: per invariant `y` and
//!   transition `t` the conservation identity
//!   `Σ_p y_p·(post[p,t] − pre[p,t]) = 0`, plus one initial-charge
//!   identity `Σ_p y_p·m0_p = b` per invariant, each built as a
//!   closed term tree over the net rows and discharged as
//!   `constExactEvalTrue` — stored term trees and claim rows are
//!   unrepresentable in the vocabulary, and a certificate with no
//!   invariants, or an all-zero invariant vector, REFUSES (the
//!   family's own vacuous-accept class: `y = 0` satisfies every
//!   identity). The count gate binds the enumeration to
//!   `K·(T+1)`.
//! - **gym v0** (`reprovocab::gym`, staged Qtsl/QtslCert/Dtmc revision
//!   pins): the certificate is a whole System + Spec + judgment +
//!   proof row set (kernel and policy mechanisms in a SysWire closed
//!   loop, the reach-by-deadline spec, QSat, and the backward-induction
//!   table under a `QDeadlineTable` rule node); the checker ENUMERATES
//!   the `QDeadlineTable` nodes from the rows and discharges
//!   `qtsl_deadline_table` per node through the provider's deadline
//!   walk — WF/B/S/C recomputed from the node's closure alone, with
//!   absorbing self-loops determined from marks, never stored. Zero
//!   nodes refuse (the certified-Gymnasium hitting lane, exact and
//!   dyadic — dyadic tables embed exactly in Q).
//!
//! - **gym reward-table v0** (`reprovocab::gymrw_v0`): the
//!   certificate carries PRIMARY DATA ONLY — dimensions, an initial
//!   distribution, outcome-row kernel rows, policy rows, table
//!   numerator rows over per-time denominators, and the claimed
//!   bound. The checker CONSTRUCTS the entire obligation set from
//!   the dimensions and discharges it as one `gymRwTableValid` walk
//!   per certificate element ([`qtsl_geolog_provider::gymrw`] —
//!   well-formedness, boundary, step, and claim-mixture recomputed
//!   in exact integer arithmetic; fixed-point certificates embed
//!   with every per-time denominator = 2^k). Stored claim rows are
//!   unrepresentable; a certificate with no `GymRwCert` element
//!   REFUSES (the vacuous-accept class, killed at the grammar
//!   level).
//!
//! - **baked v1** (`reprovocab::baked`, the DERIVED vocabulary): two
//!   modes share the derivation. A **chain container** (empty
//!   prerequisite table — the store extracts) is the baked vocabulary
//!   itself: envelopes verified, the pinned closure revision located
//!   (qc or dc), the whole chain loaded under full meta-schema
//!   conformance, the index derived from the decoded declaration rows,
//!   and provider-family resolution reported. A **certificate
//!   container** whose prerequisite table names a baked closure
//!   revision discharges its claim rows against that derived index —
//!   the roster is every side-condition relation the revision
//!   declares, so a claim row the provider cannot discharge refuses
//!   loudly rather than passing as content, and a container with no
//!   claim rows refuses (the vacuous-accept class).
//!
//! - **staged closures** (`--staged-chain <chain.glc>`, repeatable):
//!   the baked-cert shape over an EXPLICITLY loaded chain — a sealed
//!   closure that is not in the baked roster (staged revision-event
//!   passengers under test, e.g. the DtmcAbsorb species). The chain's
//!   envelopes verify self-contained, its sealed revision is located
//!   structurally (the sole commit whose deps are exactly the two
//!   goldens), and its vocabulary derives from its own bytes;
//!   certificate containers naming that revision in their
//!   prerequisite tables then discharge against the staged index.
//!   Nothing resolves without the flag, and no baked pin is consulted
//!   or touched — defaults are exactly the roster's.
//!
//! Adding a family is one `Mode` arm + its check fn; the container
//! grammar, envelope verification, and verdict assembly are shared.
//!
//! Scope honesty: this is side-condition discharge over sealed bytes
//! through the engine's ground-provider seam plus full envelope
//! verification. Theory-conformance checking of the constructor rows
//! against staged theory commits (the engine-native chase, and with
//! it the structural rule checks of the BL proof calculus — ax/ande/
//! ore formula equalities) arrives with the staged-vocabulary
//! successor; the reference lane and the certified checker cover the
//! structural stratum today.
//!
//! Trust posture: the signature authenticates provenance framing
//! only — reproduction artifacts are sealed with a public key, so the
//! mathematics carries the verdict: tampered content either breaks
//! the envelope (integrity refusal) or re-seals into rows whose
//! obligations the provider evaluates FALSE.
//!
//! usage: glc-check [--gym | --gym-rw | --gym-eproc | --baked-chain |
//!                   --baked-cert | --staged-cert]
//!                  [--staged-chain <chain.glc>]...
//!                  [--expect-modes N | --expect-claims name=N,...]
//!                  [--timings <file>] <file.glc>...
//! (the bare mode flags assert the prerequisite table names that
//! family's vocabulary — a mode expectation for manifest-driven
//! callers, not a selector: the prerequisite table always decides the
//! mode.)
//!
//! Batch amortization: one invocation checks any number of files, and
//! the per-process costs — the static vocabulary/provider roster built
//! at startup, and the baked-vocabulary derivation performed lazily
//! once per closure revision on first contact — are paid once and
//! shared by every file aboard. Verdicts are per-file and independent
//! of batching: one invocation over N files prints byte-identical
//! verdict lines to the concatenation of N single-file invocations,
//! with the same exit-code semantics (the committed conformance
//! battery in `tests/glc_baked.rs` holds this equality; cost may
//! change, verdicts may not). `--timings <file>` writes a small JSON
//! receipt decomposing the invocation — startup, each baked-kit
//! derivation keyed by its closure revision, and each file's own
//! check wall with any first-contact derivation excluded — as pure
//! observation: stdout and the exit code are unchanged by the flag.
//!
//! One verdict line per file:
//!   `<name> ACCEPT commits=1 ops=N claims farkasCombinationValid=63/63 …`
//!   `<name> ACCEPT commits=1 ops=N obligations allForwardDiffBernCoeffsSatisfyP=9/9`
//!   `<name> ACCEPT commits=1 ops=N claims spdeClaimValid=2/2 …`
//!   `<name> REFUSE <locus>: <detail>`
//!   `<name> FAIL <relation> obligation <k> does not hold`
//! `--expect-modes N` additionally requires each claim relation to
//! hold exactly N times (guards whole-mode/whole-node deletion, which
//! per-obligation discharge alone cannot see); `--expect-claims`
//! names an exact per-relation count table for families whose claim
//! relations have distinct multiplicities. Exit 0 iff every file
//! ACCEPTs.

use geolog_envelope::body::Op;
use geolog_envelope::Value;
use geolog_envelope::{Literal, LiteralView};
use geolog_ground_api::Verdict;
use qtsl_geolog_provider::container::{hex32, parse_container, verify_commits, Container};
use qtsl_geolog_provider::reprovocab::baked::{
    derive_baked_vocab, resolve_baked_rev, staged_revision_of_chain, BakedVocab,
    BAKED_COMPARISONS_CHID, BAKED_DC_V1_REV, BAKED_GENESIS_CHID, BAKED_QC_V1_REV,
};
use qtsl_geolog_provider::reprovocab::bl::{
    bl_v0_indexes, BL_CERT_V0_REV, BL_STACK_V0_REV, BL_V0_OBLIGATIONS,
};
use qtsl_geolog_provider::reprovocab::gym::{
    gym_v0_indexes, GYM_DTMC_V0_REV, GYM_QTSLCERT_V0_REV, GYM_QTSL_V0_REV, GYM_V0_OBLIGATIONS,
};
use qtsl_geolog_provider::reprovocab::{
    fluid_v0, gymeproc_v0, gymrw_v0, petri_v0, spde_v0, FLUID_V0_CLAIMS, FLUID_V0_REV,
    GYMEPROC_V0_CLAIMS, GYMEPROC_V0_REV, GYMRW_V0_CLAIMS, GYMRW_V0_REV, PETRI_V0_CLAIMS,
    PETRI_V0_REV, SPDE_V0_CLAIMS, SPDE_V0_REV,
};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use qtsl_geolog_provider::{QtslGroundProvider, QtslVocab};
use std::collections::HashMap;
use std::time::Instant;

/// The semantics revision this checker binary claims coverage of
/// (provider metadata; bumped with the vocabulary version).
const CHECKER_SEMANTICS_REV: [u8; 32] = [0x2F; 32];

/// Per-relation tallies for one file.
#[derive(Default)]
struct Tally {
    holds: usize,
    fails: usize,
    refused: Vec<String>,
}

/// Encode one row Value into a provider cell.
fn enc_val(v: &Value) -> Vec<u8> {
    let mut buf = Vec::new();
    v.encode(&mut buf);
    buf
}

/// Discharge one enumerated obligation through the provider, tallied
/// under its relation.
fn discharge_into(
    tallies: &mut HashMap<&'static str, Tally>,
    provider: &QtslGroundProvider,
    rows: &CertRows,
    name: &'static str,
    local: geolog_ground_api::LocalId,
    cells: Vec<Vec<u8>>,
) {
    let t = tallies.entry(name).or_default();
    let refs: Vec<&[u8]> = cells.iter().map(|c| c.as_slice()).collect();
    match provider.filter_rows(local, &refs, rows) {
        Verdict::Holds => t.holds += 1,
        Verdict::Fails => t.fails += 1,
        Verdict::Refused(r) => t.refused.push(r),
    }
}

/// Which pinned vocabulary a container's prerequisite table names.
enum Mode {
    Fluid,
    Bl,
    Spde,
    Petri,
    Gym,
    GymRw,
    GymEproc,
    /// A self-contained theory-chain container (empty prerequisite
    /// table): the baked vocabulary chain itself, validated end to
    /// end — envelopes, full meta-schema conformance, the pin gate,
    /// and provider-family resolution over the derived index.
    BakedChain,
    /// A certificate container whose prerequisite table names a baked
    /// closure revision; claim rows discharge against the DERIVED
    /// index (the pin the table names selects qc or dc).
    BakedCert([u8; 32]),
    /// A certificate container whose prerequisite table names a
    /// STAGED closure revision — one loaded explicitly through
    /// `--staged-chain <file.glc>` (a chain container carrying a
    /// sealed closure that is NOT in the baked roster: staged
    /// revision-event passengers under test). Same discharge shape as
    /// the baked-cert lane, against the staged chain's derived index;
    /// nothing resolves without the explicit flag, and no baked pin
    /// is consulted or touched.
    StagedCert([u8; 32]),
}

/// The stable tag a `--<tag>` mode flag asserts (drivers dispatch on
/// their manifest's `mode_flag` field; the flag pins the expected
/// family, and a mismatching container refuses rather than silently
/// riding the auto-classifier).
fn mode_tag(m: &Mode) -> &'static str {
    match m {
        Mode::Fluid => "fluid",
        Mode::Bl => "bl",
        Mode::Spde => "spde",
        Mode::Petri => "petri",
        Mode::Gym => "gym",
        Mode::GymRw => "gym-rw",
        Mode::GymEproc => "gym-eproc",
        Mode::BakedChain => "baked-chain",
        Mode::BakedCert(_) => "baked-cert",
        Mode::StagedCert(_) => "staged-cert",
    }
}

/// The count expectation, applied per file family.
enum Expect {
    None,
    /// Every family claim relation holds exactly N times.
    Modes(usize),
    /// Exact per-relation counts.
    Claims(HashMap<String, usize>),
}

impl Expect {
    fn for_name(&self, name: &str) -> Option<usize> {
        match self {
            Expect::None => None,
            Expect::Modes(m) => Some(*m),
            Expect::Claims(map) => map.get(name).copied(),
        }
    }
}

// (Envelope verification and the container parser live in
// `qtsl_geolog_provider::container` — shared with the derived baked
// vocabulary; still independent of the producer's writer.)

/// Claim-row discharge shared by the fluid and SPDE lanes: every
/// relation-instance row of a declared side-condition relation is
/// re-evaluated through the provider.
fn check_claim_rows(
    c: &Container,
    provider: &QtslGroundProvider,
    claim_chids: &HashMap<Chid, &'static str>,
    revs: &[[u8; 32]],
    claim_roster: &[&'static str],
    expect: &Expect,
) -> Result<String, String> {
    let commits = verify_commits(c, revs)?;
    let mut tallies: HashMap<&'static str, Tally> = HashMap::new();
    let mut total_ops = 0usize;

    for vc in &commits {
        total_ops += vc.ops.len();
        let rows = CertRows::from_ops(&vc.ops, vc.own, &vc.deps);

        for op in &vc.ops {
            let Op::Rela { rel, args } = op else {
                continue;
            };
            let chid = match rel {
                geolog_envelope::ElemRef::External { dep_index, counter } => {
                    let Some(rev) = vc.deps.get(*dep_index as usize) else {
                        return Err(format!("claim rel dep_index {dep_index} out of range"));
                    };
                    (*rev, *counter)
                }
                other => {
                    return Err(format!("claim rel ref not external: {other:?}"));
                }
            };
            let Some(name) = claim_chids.get(&chid) else {
                // A relation row outside the claim roster (e.g. simplex
                // membership data) is content, not a claim.
                continue;
            };
            let Some(local) = provider.local_by_name(name) else {
                return Err(format!("claim relation `{name}` not claimed by provider"));
            };
            let cells: Vec<Vec<u8>> = args
                .iter()
                .map(|v| {
                    let mut buf = Vec::new();
                    v.encode(&mut buf);
                    buf
                })
                .collect();
            let refs: Vec<&[u8]> = cells.iter().map(|c| c.as_slice()).collect();
            let t = tallies.entry(name).or_default();
            match provider.filter_rows(local, &refs, &rows) {
                Verdict::Holds => t.holds += 1,
                Verdict::Fails => t.fails += 1,
                Verdict::Refused(r) => t.refused.push(r),
            }
        }
    }
    assemble_verdict(
        "claims",
        claim_roster,
        tallies,
        commits.len(),
        total_ops,
        expect,
    )
}

fn check_bl(
    c: &Container,
    provider: &QtslGroundProvider,
    fields: &BlFieldChids,
    expect: &Expect,
) -> Result<String, String> {
    let commits = verify_commits(c, &[BL_STACK_V0_REV, BL_CERT_V0_REV])?;
    let mut tallies: HashMap<&'static str, Tally> = HashMap::new();
    let mut total_ops = 0usize;
    let local_of = |name: &'static str| -> Result<_, String> {
        provider
            .local_by_name(name)
            .ok_or_else(|| format!("claim relation `{name}` not claimed by provider"))
    };
    let l_cone = local_of("allForwardDiffBernCoeffsSatisfyP")?;
    let l_farkas = local_of("farkasCombinationValid")?;
    let l_syz = local_of("syzygyCombinationValid")?;
    let l_form = local_of("syzygyConclusionFormRel")?;
    let l_enc = local_of("enclosureWitnessValid")?;
    let l_conf = local_of("promiseContractConfined")?;
    let l_sep = local_of("promiseWiresSeparated")?;

    for vc in &commits {
        total_ops += vc.ops.len();
        let rows = CertRows::from_ops(&vc.ops, vc.own, &vc.deps);

        // One pass over the funa rows: (a) group the PBernCone field
        // rows by node; (b) index every walked unary field row by
        // (field, encoded-arg) — duplicates refuse (a second value for
        // the same field of the same node is never resolvable).
        let mut nodes: Vec<(Vec<u8>, HashMap<&'static str, Value>)> = Vec::new();
        let mut anchors: Vec<(&'static str, Value)> = Vec::new();
        let mut index: HashMap<(&'static str, Vec<u8>), Option<Value>> = HashMap::new();
        for op in &vc.ops {
            let Op::Funa { fun, args, value } = op else {
                continue;
            };
            let geolog_envelope::ElemRef::External { dep_index, counter } = fun else {
                continue;
            };
            let Some(rev) = vc.deps.get(*dep_index as usize) else {
                continue;
            };
            let chid = (*rev, *counter);
            if args.len() == 1 {
                if let Some(field) = fields.walked_name_of(chid) {
                    let mut key = Vec::new();
                    args[0].encode(&mut key);
                    index
                        .entry((field, key))
                        .and_modify(|slot| *slot = None) // duplicate → poisoned
                        .or_insert_with(|| Some(value.clone()));
                }
                if let Some(kind) = fields.anchor_kind_of(chid) {
                    anchors.push((kind, args[0].clone()));
                }
            }
            let Some(field) = fields.cone_name_of(chid) else {
                continue;
            };
            if args.len() != 1 {
                continue;
            }
            let mut key = Vec::new();
            args[0].encode(&mut key);
            let slot = match nodes.iter_mut().find(|(k, _)| *k == key) {
                Some((_, m)) => m,
                None => {
                    nodes.push((key, HashMap::new()));
                    &mut nodes.last_mut().unwrap().1
                }
            };
            slot.insert(field, value.clone());
        }

        // Walk one unary field hop: field(arg-value) — refusing on a
        // missing row and on a duplicated (poisoned) row.
        let get = |field: &'static str, arg: &Value| -> Result<Value, String> {
            match index.get(&(field, enc_val(arg))) {
                Some(Some(v)) => Ok(v.clone()),
                Some(None) => Err(format!("`{field}` row duplicated for one subject")),
                None => Err(format!("no `{field}` row for the node's chain")),
            }
        };

        // --- PBernCone: the coefficient sweep (the landed F3 lane) ---
        for (_, node) in &nodes {
            // The anchor is the simplex field; a node without it is
            // not an obligation site (and the count gate downstream
            // catches anchor deletion).
            if !node.contains_key("simplex") {
                continue;
            }
            // F_COEFFS bytewise field order: S, degree, polynomial,
            // predicate, simplex.
            let mut cells: Vec<Vec<u8>> = Vec::with_capacity(5);
            let mut missing = None;
            for f in ["S", "degree", "polynomial", "predicate", "simplex"] {
                match node.get(f) {
                    Some(v) => cells.push(enc_val(v)),
                    None => missing = Some(f),
                }
            }
            if let Some(f) = missing {
                tallies
                    .entry("allForwardDiffBernCoeffsSatisfyP")
                    .or_default()
                    .refused
                    .push(format!("PBernCone node missing field `{f}`"));
                continue;
            }
            discharge_into(
                &mut tallies,
                provider,
                &rows,
                "allForwardDiffBernCoeffsSatisfyP",
                l_cone,
                cells,
            );
        }

        // --- the applicative node kinds (the F6 lean-route lane) ---
        for (kind, node) in &anchors {
            match *kind {
                // anchor: PFarkas/combinationCoeffs. Premise = the
                // node's own judgment pre (Proof/concludes →
                // Judgment/pre) — never a carried formula.
                "farkas" => {
                    let r = (|| -> Result<Vec<Vec<u8>>, String> {
                        let cc = get("PFarkas/combinationCoeffs", node)?;
                        let concl = get("PFarkas/conclusion", node)?;
                        let proof = get("PFarkas/proof", node)?;
                        let judgment = get("Proof/concludes", &proof)?;
                        let pre = get("Judgment/pre", &judgment)?;
                        Ok(vec![enc_val(&cc), enc_val(&concl), enc_val(&pre)])
                    })();
                    match r {
                        Ok(cells) => discharge_into(
                            &mut tallies,
                            provider,
                            &rows,
                            "farkasCombinationValid",
                            l_farkas,
                            cells,
                        ),
                        Err(e) => tallies
                            .entry("farkasCombinationValid")
                            .or_default()
                            .refused
                            .push(e),
                    }
                }
                // anchor: PSyzygy/combinationCoeffs. Two obligations
                // per node: the combination replay (node-arg walk) and
                // the conclusion-form tie against the node's own
                // judgment post.
                "syzygy" => {
                    discharge_into(
                        &mut tallies,
                        provider,
                        &rows,
                        "syzygyCombinationValid",
                        l_syz,
                        vec![enc_val(node)],
                    );
                    let r = (|| -> Result<Vec<Vec<u8>>, String> {
                        let concl = get("PSyzygy/conclusion", node)?;
                        let proof = get("PSyzygy/proof", node)?;
                        let judgment = get("Proof/concludes", &proof)?;
                        let post = get("Judgment/post", &judgment)?;
                        Ok(vec![enc_val(&concl), enc_val(&post)])
                    })();
                    match r {
                        Ok(cells) => discharge_into(
                            &mut tallies,
                            provider,
                            &rows,
                            "syzygyConclusionFormRel",
                            l_form,
                            cells,
                        ),
                        Err(e) => tallies
                            .entry("syzygyConclusionFormRel")
                            .or_default()
                            .refused
                            .push(e),
                    }
                }
                // anchor: PEnclosure/concludes — the concluded
                // EncJudgment is the relation's subject.
                "enclosure" => match get("PEnclosure/concludes", node) {
                    Ok(judgment) => discharge_into(
                        &mut tallies,
                        provider,
                        &rows,
                        "enclosureWitnessValid",
                        l_enc,
                        vec![enc_val(&judgment)],
                    ),
                    Err(e) => tallies
                        .entry("enclosureWitnessValid")
                        .or_default()
                        .refused
                        .push(e),
                },
                // anchor: PPromise/contract — the node carries both
                // wire obligations (node-arg walks).
                "promise" => {
                    discharge_into(
                        &mut tallies,
                        provider,
                        &rows,
                        "promiseContractConfined",
                        l_conf,
                        vec![enc_val(node)],
                    );
                    discharge_into(
                        &mut tallies,
                        provider,
                        &rows,
                        "promiseWiresSeparated",
                        l_sep,
                        vec![enc_val(node)],
                    );
                }
                _ => unreachable!(),
            }
        }
    }
    assemble_verdict(
        "obligations",
        &BL_V0_OBLIGATIONS,
        tallies,
        commits.len(),
        total_ops,
        expect,
    )
}

fn assemble_verdict(
    kind: &str,
    roster: &[&'static str],
    mut tallies: HashMap<&'static str, Tally>,
    commits: usize,
    total_ops: usize,
    expect: &Expect,
) -> Result<String, String> {
    let mut parts = Vec::new();
    let mut ok = true;
    for name in roster {
        let t = tallies.remove(name).unwrap_or_default();
        let n = t.holds + t.fails;
        if let Some(r) = t.refused.first() {
            return Err(format!("{kind} `{name}` refused: {r}"));
        }
        if t.fails > 0 {
            ok = false;
        }
        if let Some(m) = expect.for_name(name) {
            if n != m || t.holds != m {
                ok = false;
            }
            parts.push(format!("{name}={}/{m}", t.holds));
        } else {
            parts.push(format!("{name}={}/{n}", t.holds));
        }
    }
    let verdict = if ok { "ACCEPT" } else { "FAIL" };
    Ok(format!(
        "{verdict} commits={commits} ops={total_ops} {kind} {}",
        parts.join(" ")
    ))
}

/// The BL vocabulary's PBernCone field chids, resolved once at startup.
struct BlFieldChids {
    /// PBernCone's five sweep fields, bare cell names.
    cone: Vec<(Chid, &'static str)>,
    /// Unary field rows the applicative walks read, prefixed names.
    walked: Vec<(Chid, &'static str)>,
    /// Node-discovery anchors: (field chid, node kind).
    anchors: Vec<(Chid, &'static str)>,
}

impl BlFieldChids {
    fn build() -> BlFieldChids {
        let (qs, _) = bl_v0_indexes();
        let f =
            |name: &str| -> Chid { qs.fun(name).expect("BL vocabulary declares the field").chid };
        let mut cone = Vec::new();
        for (name, field) in [
            ("PBernCone/S", "S"),
            ("PBernCone/degree", "degree"),
            ("PBernCone/polynomial", "polynomial"),
            ("PBernCone/predicate", "predicate"),
            ("PBernCone/simplex", "simplex"),
        ] {
            cone.push((f(name), field));
        }
        let mut walked = Vec::new();
        for name in [
            "PFarkas/combinationCoeffs",
            "PFarkas/conclusion",
            "PFarkas/proof",
            "PSyzygy/conclusion",
            "PSyzygy/proof",
            "PEnclosure/concludes",
            "Proof/concludes",
            "Judgment/pre",
            "Judgment/post",
        ] {
            walked.push((f(name), name));
        }
        // Discovery anchors: one field per node kind, the field the
        // producer's obligation counter uses (the count-gate twin).
        let anchors = vec![
            (f("PFarkas/combinationCoeffs"), "farkas"),
            (f("PSyzygy/combinationCoeffs"), "syzygy"),
            (f("PEnclosure/concludes"), "enclosure"),
            (f("PPromise/contract"), "promise"),
        ];
        BlFieldChids {
            cone,
            walked,
            anchors,
        }
    }
    fn cone_name_of(&self, chid: Chid) -> Option<&'static str> {
        self.cone.iter().find(|(c, _)| *c == chid).map(|(_, n)| *n)
    }
    fn walked_name_of(&self, chid: Chid) -> Option<&'static str> {
        self.walked
            .iter()
            .find(|(c, _)| *c == chid)
            .map(|(_, n)| *n)
    }
    fn anchor_kind_of(&self, chid: Chid) -> Option<&'static str> {
        self.anchors
            .iter()
            .find(|(c, _)| *c == chid)
            .map(|(_, n)| *n)
    }
}

/// The Petri vocabulary's chids, resolved once at startup.
struct PetriChids {
    pnet_sort: Chid,
    pinv_sort: Chid,
    term_sort: Chid,
    places: Chid,
    transitions: Chid,
    invariants: Chid,
    pre: Chid,
    post: Chid,
    m0: Chid,
    inv_net: Chid,
    inv_index: Chid,
    inv_coeff: Chid,
    inv_charge: Chid,
    tconst: Chid,
    tadd: Chid,
    tsub: Chid,
    tmul: Chid,
}

impl PetriChids {
    fn build(ix: &qtsl_geolog_provider::theory::TheoryIndex) -> PetriChids {
        let f = |name: &str| -> Chid {
            ix.fun(name)
                .expect("petri vocabulary declares the field")
                .chid
        };
        let s = |name: &str| -> Chid { ix.sort(name).expect("petri vocabulary declares the sort") };
        PetriChids {
            pnet_sort: s("PNet"),
            pinv_sort: s("PInv"),
            term_sort: s("Term"),
            places: f("PNet/places"),
            transitions: f("PNet/transitions"),
            invariants: f("PNet/invariants"),
            pre: f("PNet/pre"),
            post: f("PNet/post"),
            m0: f("PNet/m0"),
            inv_net: f("PInv/net"),
            inv_index: f("PInv/index"),
            inv_coeff: f("PInv/coeff"),
            inv_charge: f("PInv/charge"),
            tconst: f("TConst"),
            tadd: f("TAdd"),
            tsub: f("TSub"),
            tmul: f("TMul"),
        }
    }
}

/// Checker-side term-row context: the constructed obligations'
/// evaluation vehicle. The certificate carries no term rows — these
/// ops are the CHECKER's, built fresh per obligation from the net's
/// primary data and evaluated through the same provider seam.
struct PetriEmitter<'a> {
    ops: Vec<Op>,
    deps: Vec<[u8; 32]>,
    chids: &'a PetriChids,
}

impl<'a> PetriEmitter<'a> {
    fn new(chids: &'a PetriChids) -> PetriEmitter<'a> {
        PetriEmitter {
            ops: Vec::new(),
            deps: vec![PETRI_V0_REV],
            chids,
        }
    }
    fn ext(&self, chid: Chid) -> geolog_envelope::ElemRef {
        let dep_index = self
            .deps
            .iter()
            .position(|h| *h == chid.0)
            .expect("chid homed in deps") as u32;
        geolog_envelope::ElemRef::External {
            dep_index,
            counter: chid.1,
        }
    }
    fn lref(e: u32) -> Value {
        Value::Ref(geolog_envelope::ElemRef::Local(e))
    }
    fn ctor(&mut self, fun: Chid, args: Vec<Value>) -> u32 {
        let e = self.ops.len() as u32;
        self.ops.push(Op::Elta {
            sort: self.ext(self.chids.term_sort),
        });
        self.ops.push(Op::Funa {
            fun: self.ext(fun),
            args,
            value: Self::lref(e),
        });
        e
    }
    fn tconst(&mut self, lit: &Literal) -> u32 {
        self.ctor(self.chids.tconst, vec![Value::Lit(lit.clone())])
    }
    fn node2(&mut self, fun: Chid, l: u32, r: u32) -> u32 {
        self.ctor(fun, vec![Self::lref(l), Self::lref(r)])
    }
    /// Right-nested Add chain over already-emitted term ids; the
    /// empty sum is `TConst 0` (the battery's `sum` transcribed).
    fn sum(&mut self, terms: Vec<u32>, zero: &Literal) -> u32 {
        match terms.split_last() {
            None => self.tconst(zero),
            Some((last, init)) => {
                let mut acc = *last;
                for t in init.iter().rev() {
                    acc = self.node2(self.chids.tadd, *t, acc);
                }
                acc
            }
        }
    }
    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, [0xF8; 32], &self.deps)
    }
}

/// The Petri P-invariant lane: primary data in, obligations
/// constructed, `constExactEvalTrue` discharged per obligation. See
/// the module docs' fourth vocabulary bullet for the trust story.
fn check_petri(
    c: &Container,
    provider: &QtslGroundProvider,
    chids: &PetriChids,
    expect: &Expect,
) -> Result<String, String> {
    let commits = verify_commits(c, &[PETRI_V0_REV])?;
    let mut tallies: HashMap<&'static str, Tally> = HashMap::new();
    let mut total_ops = 0usize;
    let l_cee = provider
        .local_by_name("constExactEvalTrue")
        .ok_or_else(|| "claim relation `constExactEvalTrue` not claimed by provider".to_string())?;

    let zero = Literal::q(0, 1).expect("canonical zero");
    let zero_enc = {
        let mut b = Vec::new();
        Value::Lit(zero.clone()).encode(&mut b);
        b
    };
    let is_zero = |l: &Literal| -> bool {
        let mut b = Vec::new();
        Value::Lit(l.clone()).encode(&mut b);
        b == zero_enc
    };
    let as_nat = |v: &Value, what: &str| -> Result<u64, String> {
        match v {
            Value::Lit(l) => match l.view() {
                LiteralView::Nat(n) => Ok(n),
                other => Err(format!("{what}: expected a Nat literal, got {other:?}")),
            },
            other => Err(format!("{what}: expected a Nat literal, got {other:?}")),
        }
    };
    let as_q = |v: &Value, what: &str| -> Result<Literal, String> {
        match v {
            Value::Lit(l) => match l.view() {
                LiteralView::Q { .. } => Ok(l.clone()),
                other => Err(format!("{what}: expected a Q literal, got {other:?}")),
            },
            other => Err(format!("{what}: expected a Q literal, got {other:?}")),
        }
    };
    let as_local = |v: &Value, what: &str| -> Result<u32, String> {
        match v {
            Value::Ref(geolog_envelope::ElemRef::Local(e)) => Ok(*e),
            other => Err(format!(
                "{what}: expected a local element ref, got {other:?}"
            )),
        }
    };

    for vc in &commits {
        total_ops += vc.ops.len();

        // ---- parse: the closed primary-data grammar. Anything the
        // grammar does not name REFUSES — a Petri certificate has no
        // lawful claim row, term row, or foreign element.
        let mut nets: Vec<u32> = Vec::new();
        let mut invs: Vec<u32> = Vec::new();
        let mut places: HashMap<u32, u64> = HashMap::new();
        let mut transitions: HashMap<u32, u64> = HashMap::new();
        let mut declared_invs: HashMap<u32, u64> = HashMap::new();
        let mut pre: HashMap<(u32, u64, u64), Literal> = HashMap::new();
        let mut post: HashMap<(u32, u64, u64), Literal> = HashMap::new();
        let mut m0: HashMap<(u32, u64), Literal> = HashMap::new();
        let mut inv_net: HashMap<u32, u32> = HashMap::new();
        let mut inv_index: HashMap<u32, u64> = HashMap::new();
        let mut inv_charge: HashMap<u32, Literal> = HashMap::new();
        let mut coeff: HashMap<(u32, u64), Literal> = HashMap::new();

        let resolve = |r: &geolog_envelope::ElemRef| -> Result<Chid, String> {
            match r {
                geolog_envelope::ElemRef::External { dep_index, counter } => {
                    let Some(rev) = vc.deps.get(*dep_index as usize) else {
                        return Err(format!("dep_index {dep_index} out of range"));
                    };
                    Ok((*rev, *counter))
                }
                other => Err(format!("reference not external: {other:?}")),
            }
        };
        fn put<K: std::hash::Hash + Eq + std::fmt::Debug, V>(
            map: &mut HashMap<K, V>,
            k: K,
            v: V,
            what: &str,
        ) -> Result<(), String> {
            if map.contains_key(&k) {
                return Err(format!("{what}: duplicate row for {k:?}"));
            }
            map.insert(k, v);
            Ok(())
        }

        for (i, op) in vc.ops.iter().enumerate() {
            let local = i as u32;
            match op {
                Op::Elta { sort } => {
                    let s = resolve(sort)?;
                    if s == chids.pnet_sort {
                        nets.push(local);
                    } else if s == chids.pinv_sort {
                        invs.push(local);
                    } else {
                        return Err(format!(
                            "op {i}: element of a sort outside the Petri primary-data grammar"
                        ));
                    }
                }
                Op::Funa { fun, args, value } => {
                    let f = resolve(fun)?;
                    if f == chids.places || f == chids.transitions || f == chids.invariants {
                        let net = as_local(&args[0], "dimension row subject")?;
                        let n = as_nat(value, "dimension row value")?;
                        let (map, what) = if f == chids.places {
                            (&mut places, "PNet/places")
                        } else if f == chids.transitions {
                            (&mut transitions, "PNet/transitions")
                        } else {
                            (&mut declared_invs, "PNet/invariants")
                        };
                        put(map, net, n, what)?;
                    } else if f == chids.pre || f == chids.post {
                        if args.len() != 3 {
                            return Err(format!("op {i}: flow row arity {}", args.len()));
                        }
                        let net = as_local(&args[0], "flow row net")?;
                        let p = as_nat(&args[1], "flow row p")?;
                        let t = as_nat(&args[2], "flow row t")?;
                        let w = as_q(value, "flow row weight")?;
                        let (map, what) = if f == chids.pre {
                            (&mut pre, "PNet/pre")
                        } else {
                            (&mut post, "PNet/post")
                        };
                        put(map, (net, p, t), w, what)?;
                    } else if f == chids.m0 {
                        if args.len() != 2 {
                            return Err(format!("op {i}: m0 row arity {}", args.len()));
                        }
                        let net = as_local(&args[0], "m0 row net")?;
                        let p = as_nat(&args[1], "m0 row p")?;
                        let w = as_q(value, "m0 row value")?;
                        put(&mut m0, (net, p), w, "PNet/m0")?;
                    } else if f == chids.inv_net {
                        let inv = as_local(&args[0], "PInv/net subject")?;
                        let net = as_local(value, "PInv/net value")?;
                        put(&mut inv_net, inv, net, "PInv/net")?;
                    } else if f == chids.inv_index {
                        let inv = as_local(&args[0], "PInv/index subject")?;
                        let k = as_nat(value, "PInv/index value")?;
                        put(&mut inv_index, inv, k, "PInv/index")?;
                    } else if f == chids.inv_coeff {
                        if args.len() != 2 {
                            return Err(format!("op {i}: coeff row arity {}", args.len()));
                        }
                        let inv = as_local(&args[0], "coeff row inv")?;
                        let p = as_nat(&args[1], "coeff row p")?;
                        let y = as_q(value, "coeff row value")?;
                        put(&mut coeff, (inv, p), y, "PInv/coeff")?;
                    } else if f == chids.inv_charge {
                        let inv = as_local(&args[0], "PInv/charge subject")?;
                        let b = as_q(value, "PInv/charge value")?;
                        put(&mut inv_charge, inv, b, "PInv/charge")?;
                    } else {
                        return Err(format!(
                            "op {i}: function row outside the Petri primary-data grammar"
                        ));
                    }
                }
                _ => {
                    return Err(format!(
                        "op {i}: op kind outside the Petri primary-data grammar \
                         (a Petri certificate has no lawful claim row)"
                    ));
                }
            }
        }

        // ---- structural gates (malformation refuses; it is never a
        // verdict).
        if nets.len() != 1 {
            return Err(format!(
                "expected exactly one PNet element, found {}",
                nets.len()
            ));
        }
        let net = nets[0];
        let np = *places
            .get(&net)
            .ok_or_else(|| "missing PNet/places row".to_string())?;
        let nt = *transitions
            .get(&net)
            .ok_or_else(|| "missing PNet/transitions row".to_string())?;
        let kd = *declared_invs
            .get(&net)
            .ok_or_else(|| "missing PNet/invariants row".to_string())?;
        if invs.is_empty() {
            return Err(
                "no PInv elements: a certificate with no invariants certifies nothing (refusing \
                 the vacuous accept)"
                    .to_string(),
            );
        }
        if kd != invs.len() as u64 {
            return Err(format!(
                "PNet/invariants declares {kd} but {} PInv elements are present",
                invs.len()
            ));
        }
        for ((n, p, t), _) in pre.iter().chain(post.iter()) {
            if *n != net {
                return Err("flow row names a foreign net".to_string());
            }
            if *p >= np || *t >= nt {
                return Err(format!("flow row ({p},{t}) out of range {np}x{nt}"));
            }
        }
        for ((n, p), _) in m0.iter() {
            if *n != net {
                return Err("m0 row names a foreign net".to_string());
            }
            if *p >= np {
                return Err(format!("m0 row place {p} out of range {np}"));
            }
        }
        let mut indices: Vec<u64> = Vec::with_capacity(invs.len());
        for inv in &invs {
            let Some(n) = inv_net.get(inv) else {
                return Err("PInv without a PInv/net row".to_string());
            };
            if *n != net {
                return Err("PInv names a foreign net".to_string());
            }
            let Some(k) = inv_index.get(inv) else {
                return Err("PInv without a PInv/index row".to_string());
            };
            indices.push(*k);
            if !inv_charge.contains_key(inv) {
                return Err("PInv without a PInv/charge row".to_string());
            }
        }
        {
            let mut sorted = indices.clone();
            sorted.sort_unstable();
            let want: Vec<u64> = (0..invs.len() as u64).collect();
            if sorted != want {
                return Err(format!(
                    "PInv/index set {sorted:?} is not exactly 0..{}",
                    invs.len()
                ));
            }
        }
        for ((inv, p), _) in coeff.iter() {
            if !invs.contains(inv) {
                return Err("coeff row names a foreign invariant".to_string());
            }
            if *p >= np {
                return Err(format!("coeff row place {p} out of range {np}"));
            }
        }
        for inv in &invs {
            let support_nonzero = coeff.iter().any(|((i, _), y)| i == inv && !is_zero(y));
            if !support_nonzero {
                return Err(format!(
                    "invariant {} is the zero vector: every identity holds vacuously — refused",
                    inv_index[inv]
                ));
            }
        }

        // ---- obligations, enumerated from the dimensions (never
        // from what happens to be present): per invariant, T
        // conservation identities + one initial charge.
        let mut order: Vec<u32> = invs.clone();
        order.sort_unstable_by_key(|inv| inv_index[inv]);
        for inv in &order {
            for t in 0..nt {
                let mut em = PetriEmitter::new(chids);
                let mut terms: Vec<u32> = Vec::new();
                for p in 0..np {
                    let pw = pre.get(&(net, p, t));
                    let ow = post.get(&(net, p, t));
                    let pw_nz = pw.map(|w| !is_zero(w)).unwrap_or(false);
                    let ow_nz = ow.map(|w| !is_zero(w)).unwrap_or(false);
                    if !pw_nz && !ow_nz {
                        continue;
                    }
                    let y = coeff.get(&(*inv, p)).unwrap_or(&zero);
                    let yc = em.tconst(y);
                    let oc = em.tconst(ow.unwrap_or(&zero));
                    let pc = em.tconst(pw.unwrap_or(&zero));
                    let diff = em.node2(chids.tsub, oc, pc);
                    terms.push(em.node2(chids.tmul, yc, diff));
                }
                let l = em.sum(terms, &zero);
                let r = em.tconst(&zero);
                dispatch_cee(&mut tallies, provider, &em, l_cee, l, r);
            }
            // The initial charge: Σ over the invariant's support.
            let mut em = PetriEmitter::new(chids);
            let mut terms: Vec<u32> = Vec::new();
            for p in 0..np {
                let Some(y) = coeff.get(&(*inv, p)) else {
                    continue;
                };
                if is_zero(y) {
                    continue;
                }
                let yc = em.tconst(y);
                let mc = em.tconst(m0.get(&(net, p)).unwrap_or(&zero));
                terms.push(em.node2(chids.tmul, yc, mc));
            }
            let l = em.sum(terms, &zero);
            let r = em.tconst(&inv_charge[inv]);
            dispatch_cee(&mut tallies, provider, &em, l_cee, l, r);
        }
    }
    assemble_verdict(
        "claims",
        &PETRI_V0_CLAIMS,
        tallies,
        commits.len(),
        total_ops,
        expect,
    )
}

/// Dispatch one constructed `constExactEvalTrue {bowtie: Eq, l, r}`
/// over the checker's own row context.
fn dispatch_cee(
    tallies: &mut HashMap<&'static str, Tally>,
    provider: &QtslGroundProvider,
    em: &PetriEmitter,
    local: geolog_ground_api::LocalId,
    l: u32,
    r: u32,
) {
    let rows = em.rows();
    // bowtie 2 = Eq (the catalogue's Cmp order).
    let args = [
        Value::Lit(Literal::nat(2)),
        PetriEmitter::lref(l),
        PetriEmitter::lref(r),
    ];
    let cells: Vec<Vec<u8>> = args.iter().map(enc_val).collect();
    discharge_into(tallies, provider, &rows, "constExactEvalTrue", local, cells);
}

/// The gym deadline-table lane: certificates are System + Spec +
/// judgment + proof rows on the REAL staged Qtsl/QtslCert/Dtmc
/// revisions; the checker enumerates the `QDeadlineTable` rule nodes
/// from the rows and discharges `qtsl_deadline_table(node)` through
/// the provider's deadline walk (WF/B/S/C recomputed from the node's
/// closure alone — kernel groups, init mixture, policy, goal set,
/// table; absorbing self-loops determined from marks, never stored).
/// A container with no `QDeadlineTable` node REFUSES: it certifies
/// nothing (the family's vacuous-accept class).
fn check_gym(
    c: &Container,
    provider: &QtslGroundProvider,
    node_sort: Chid,
    expect: &Expect,
) -> Result<String, String> {
    let commits = verify_commits(c, &[GYM_QTSL_V0_REV, GYM_QTSLCERT_V0_REV, GYM_DTMC_V0_REV])?;
    let mut tallies: HashMap<&'static str, Tally> = HashMap::new();
    let mut total_ops = 0usize;
    let l_dl = provider
        .local_by_name("qtsl_deadline_table")
        .ok_or_else(|| {
            "claim relation `qtsl_deadline_table` not claimed by provider".to_string()
        })?;

    for vc in &commits {
        total_ops += vc.ops.len();
        let rows = CertRows::from_ops(&vc.ops, vc.own, &vc.deps);
        let mut nodes: Vec<u32> = Vec::new();
        for (i, op) in vc.ops.iter().enumerate() {
            let Op::Elta { sort } = op else { continue };
            let chid = match sort {
                geolog_envelope::ElemRef::External { dep_index, counter } => {
                    let Some(rev) = vc.deps.get(*dep_index as usize) else {
                        return Err(format!("elta sort dep_index {dep_index} out of range"));
                    };
                    (*rev, *counter)
                }
                other => {
                    return Err(format!("elta sort ref not external: {other:?}"));
                }
            };
            if chid == node_sort {
                nodes.push(i as u32);
            }
        }
        if nodes.is_empty() {
            return Err(
                "no QDeadlineTable node: a deadline container certifies nothing \
                 (refusing the vacuous accept)"
                    .to_string(),
            );
        }
        for e in nodes {
            let cell = enc_val(&Value::Ref(geolog_envelope::ElemRef::Local(e)));
            discharge_into(
                &mut tallies,
                provider,
                &rows,
                "qtsl_deadline_table",
                l_dl,
                vec![cell],
            );
        }
    }
    assemble_verdict(
        "obligations",
        &GYM_V0_OBLIGATIONS,
        tallies,
        commits.len(),
        total_ops,
        expect,
    )
}

/// The gym reward-table vocabulary's chids, resolved once at startup.
struct GymRwChids {
    cert_sort: Chid,
    funs: Vec<Chid>,
}

impl GymRwChids {
    fn build(ix: &qtsl_geolog_provider::theory::TheoryIndex) -> GymRwChids {
        let f = |name: &str| -> Chid {
            ix.fun(name)
                .expect("gymrw vocabulary declares the field")
                .chid
        };
        GymRwChids {
            cert_sort: ix.sort("GymRwCert").expect("GymRwCert sort"),
            funs: [
                "GymRwCert/ns",
                "GymRwCert/na",
                "GymRwCert/deadline",
                "GymRwCert/initDen",
                "GymRwCert/claim",
                "GymRwCert/initW",
                "GymRwCert/kden",
                "GymRwCert/kout",
                "GymRwCert/pact",
                "GymRwCert/qden",
                "GymRwCert/w",
            ]
            .iter()
            .map(|n| f(n))
            .collect(),
        }
    }
}

/// The gym reward-table lane: primary data in, the whole obligation
/// set (well-formedness / boundary / step / claim-mixture) constructed
/// from the dimensions and discharged as ONE `gymRwTableValid` walk
/// per certificate element through the provider seam. The grammar is
/// closed at this boundary: an op outside the primary-data family —
/// any relation-instance row especially — refuses on sight (a gym
/// reward certificate has no lawful claim row), and a container with
/// no certificate element refuses rather than vacuously accepting.
fn check_gymrw(
    c: &Container,
    provider: &QtslGroundProvider,
    chids: &GymRwChids,
    expect: &Expect,
) -> Result<String, String> {
    let commits = verify_commits(c, &[GYMRW_V0_REV])?;
    let mut tallies: HashMap<&'static str, Tally> = HashMap::new();
    let mut total_ops = 0usize;
    let l_walk = provider
        .local_by_name("gymRwTableValid")
        .ok_or_else(|| "claim relation `gymRwTableValid` not claimed by provider".to_string())?;

    for vc in &commits {
        total_ops += vc.ops.len();
        let rows = CertRows::from_ops(&vc.ops, vc.own, &vc.deps);

        let resolve = |r: &geolog_envelope::ElemRef| -> Result<Chid, String> {
            match r {
                geolog_envelope::ElemRef::External { dep_index, counter } => {
                    let Some(rev) = vc.deps.get(*dep_index as usize) else {
                        return Err(format!("dep_index {dep_index} out of range"));
                    };
                    Ok((*rev, *counter))
                }
                other => Err(format!("reference not external: {other:?}")),
            }
        };

        // ---- the closed primary-data grammar ------------------------
        let mut certs: Vec<u32> = Vec::new();
        for (i, op) in vc.ops.iter().enumerate() {
            match op {
                Op::Elta { sort } => {
                    if resolve(sort)? != chids.cert_sort {
                        return Err(format!(
                            "op {i}: element of a sort outside the gym reward-table \
                             primary-data grammar"
                        ));
                    }
                    certs.push(i as u32);
                }
                Op::Funa { fun, args, .. } => {
                    let f = resolve(fun)?;
                    if !chids.funs.contains(&f) {
                        return Err(format!(
                            "op {i}: function row outside the gym reward-table \
                             primary-data grammar"
                        ));
                    }
                    let Some(Value::Ref(geolog_envelope::ElemRef::Local(subj))) = args.first()
                    else {
                        return Err(format!(
                            "op {i}: row subject is not a local certificate element"
                        ));
                    };
                    if !certs.contains(subj) {
                        return Err(format!(
                            "op {i}: row subject {subj} is not a certificate element"
                        ));
                    }
                    if args.iter().skip(1).any(|a| !matches!(a, Value::Lit(_))) {
                        return Err(format!("op {i}: non-literal key cell in a data row"));
                    }
                }
                _ => {
                    return Err(format!(
                        "op {i}: op kind outside the gym reward-table primary-data \
                         grammar (a gym reward certificate has no lawful claim row)"
                    ));
                }
            }
        }
        if certs.is_empty() {
            return Err(
                "no GymRwCert element: a container with no certificate certifies nothing \
                 (refusing the vacuous accept)"
                    .to_string(),
            );
        }

        // ---- one constructed walk obligation per certificate --------
        for cert in &certs {
            let arg = Value::Ref(geolog_envelope::ElemRef::Local(*cert));
            discharge_into(
                &mut tallies,
                provider,
                &rows,
                "gymRwTableValid",
                l_walk,
                vec![enc_val(&arg)],
            );
        }
    }
    assemble_verdict(
        "claims",
        &GYMRW_V0_CLAIMS,
        tallies,
        commits.len(),
        total_ops,
        expect,
    )
}

/// The provider families that resolved over a derived index, named
/// for the chain-mode verdict line (an open list — extend as families
/// gain baked support).
fn resolved_families(v: &QtslVocab) -> Vec<&'static str> {
    let mut out = Vec::new();
    for (name, on) in [
        ("bl", v.bl.is_some()),
        ("morse", v.morse.is_some()),
        ("miranda", v.miranda.is_some()),
        ("stochwire", v.stochwire.is_some()),
        ("bagcanon", v.bagcanon.is_some()),
        ("mask", v.mask.is_some()),
        ("polycanon", v.polycanon.is_some()),
        ("syswire", v.syswire.is_some()),
        ("problog", v.problog.is_some()),
        ("barycoord", v.barycoord.is_some()),
        ("cellapp", v.cellapp.is_some()),
        ("lattice", v.lattice.is_some()),
        ("enclosure", v.enclosure.is_some()),
        ("carillon", v.carillon.is_some()),
        ("surgery", v.surgery.is_some()),
        ("promise", v.promise.is_some()),
        ("subdivide", v.subdivide.is_some()),
        ("dtype", v.dtype.is_some()),
        ("deadline", v.deadline.is_some()),
        ("spdemoment", v.spdemoment.is_some()),
        ("gymrw", v.gymrw.is_some()),
        ("gymeproc", v.gymeproc.is_some()),
        ("dabs", v.dabs.is_some()),
    ] {
        if on {
            out.push(name);
        }
    }
    out
}

/// The baked-chain lane: a self-contained theory-chain container —
/// envelope verification, the pin gate (exactly one of the two baked
/// closure revisions must be aboard), full meta-schema conformance
/// load of the whole chain, and provider-family resolution over the
/// derived index. Scope honesty: this validates the meta-schema
/// stratum (declaration conformance) and the envelope stratum; the
/// chase-level coherence gate (axiom strata over the store) is
/// `geolog check --store`'s business, not a container checker's.
fn check_baked_chain(c: &Container, expect: &Expect) -> Result<String, String> {
    if !matches!(expect, Expect::None) {
        return Err(
            "expectation_inapplicable: --expect-modes/--expect-claims name claim counts, \
             and a chain container carries no claims — refusing rather than vacuously \
             satisfying the expectation"
                .to_string(),
        );
    }
    // Self-contained: deps resolve against earlier commits only.
    let commits = verify_commits(c, &[])?;
    let total_ops: usize = commits.iter().map(|vc| vc.ops.len()).sum();
    // PRIMARY-ONLY, deliberately: a chain container must carry the
    // CURRENT event's revision (greenfield — old-event chains re-emit
    // rather than resolve; the append-only store, not this checker,
    // is where history lives).
    let qc = commits.iter().any(|vc| vc.own == BAKED_QC_V1_REV);
    let dc = commits.iter().any(|vc| vc.own == BAKED_DC_V1_REV);
    let (closure, pin) = match (qc, dc) {
        (true, false) => ("qc", BAKED_QC_V1_REV),
        (false, true) => ("dc", BAKED_DC_V1_REV),
        (true, true) => {
            return Err(
                "chain_ambiguous: both baked closure revisions in one container".to_string(),
            )
        }
        (false, false) => {
            return Err(
                "chain_unpinned: no pinned baked revision among the commits — not a \
                 baked vocabulary chain this checker recognizes"
                    .to_string(),
            )
        }
    };
    let vocab = derive_baked_vocab(pin, &commits)?;
    let qv = QtslVocab::build(&[&vocab.index]);
    let families = resolved_families(&qv);
    if families.is_empty() {
        return Err(
            "chain_unresolvable: no provider family resolves over the derived index — \
             a vocabulary no certificate could discharge against"
                .to_string(),
        );
    }
    Ok(format!(
        "ACCEPT commits={} ops={total_ops} chain closure={closure} revision={} \
         theories={} sorts={} funs={} claims={} families {}",
        commits.len(),
        hex32(&vocab.revision),
        vocab.stats.theories,
        vocab.stats.sorts,
        vocab.stats.funs,
        vocab.claims.len(),
        families.join(",")
    ))
}

/// One derived certificate-mode kit: the vocabulary, its provider,
/// and the claim-relation chid map.
struct BakedKit {
    vocab: BakedVocab,
    provider: QtslGroundProvider,
    claim_chids: HashMap<qtsl_geolog_provider::theory::Chid, String>,
}

impl BakedKit {
    /// Derive from an EXPLICIT chain container's bytes (the
    /// `--staged-chain` lane): envelopes verified self-contained, the
    /// sealed revision located structurally — the sole commit whose
    /// dep table is exactly the two goldens — and the vocabulary
    /// derived from the chain's own bytes. Returns the revision chid
    /// beside the kit (certificate containers name it in their
    /// prerequisite tables). The baked roster is never consulted.
    fn from_chain_bytes(bytes: &[u8]) -> Result<([u8; 32], BakedKit), String> {
        // One definition of "the chain's revision", shared with the
        // certificate emitter (the library's structural locator) —
        // producer and checker cannot disagree about it.
        let (pin, commits) = staged_revision_of_chain(bytes)?;
        let vocab = derive_baked_vocab(pin, &commits)
            .map_err(|e| format!("staged vocabulary derivation: {e}"))?;
        let qv = QtslVocab::build(&[&vocab.index]);
        let provider = QtslGroundProvider::new(vec![CHECKER_SEMANTICS_REV], qv);
        let mut claim_chids = HashMap::new();
        for name in &vocab.claims {
            if let Some(d) = vocab.index.fun(name) {
                claim_chids.insert(d.chid, name.clone());
            }
        }
        Ok((
            pin,
            BakedKit {
                vocab,
                provider,
                claim_chids,
            },
        ))
    }

    /// Derive from the embedded chain fixture for `pin` — resolved
    /// through the baked roster (the primary pair; retired events are
    /// deliberately NOT retained: greenfield ruling 2026-07-29 14:28 —
    /// committed corpora re-emit at the current event instead of
    /// riding old extracts).
    fn build(pin: [u8; 32]) -> Result<BakedKit, String> {
        let entry = resolve_baked_rev(&pin).ok_or_else(|| {
            format!(
                "pin_unresolvable: revision {} is not in the baked roster (classify \
                 admitted it; roster and classify have drifted)",
                hex32(&pin)
            )
        })?;
        let bytes = (entry.container)();
        let vocab = qtsl_geolog_provider::reprovocab::baked::baked_vocab_from_container(bytes, pin)
            .map_err(|e| format!("baked vocabulary derivation: {e}"))?;
        let qv = QtslVocab::build(&[&vocab.index]);
        let provider = QtslGroundProvider::new(vec![CHECKER_SEMANTICS_REV], qv);
        let mut claim_chids = HashMap::new();
        for name in &vocab.claims {
            if let Some(d) = vocab.index.fun(name) {
                claim_chids.insert(d.chid, name.clone());
            }
        }
        Ok(BakedKit {
            vocab,
            provider,
            claim_chids,
        })
    }
}

/// The baked-cert lane: claim rows discharge against the DERIVED
/// index, exactly the fluid lane's shape with two hardenings — the
/// claim roster is every side-condition relation the baked revision
/// declares (a claim row for a relation the provider does not claim
/// refuses loudly, never passes as content), and a container with no
/// claim rows refuses (the vacuous-accept class). The verdict line
/// names only relations with nonzero tallies or an explicit
/// expectation.
fn check_baked_cert(c: &Container, kit: &BakedKit, expect: &Expect) -> Result<String, String> {
    if matches!(expect, Expect::Modes(_)) {
        return Err(
            "expectation_inapplicable: --expect-modes assumes a fixed family claim \
             roster; the baked lane's roster is derived — use --expect-claims \
             name=N,..."
                .to_string(),
        );
    }
    let commits = verify_commits(
        c,
        &[
            kit.vocab.revision,
            BAKED_GENESIS_CHID,
            BAKED_COMPARISONS_CHID,
        ],
    )?;
    let mut tallies: HashMap<String, Tally> = HashMap::new();
    let mut total_ops = 0usize;
    let mut claim_rows = 0usize;

    for vc in &commits {
        total_ops += vc.ops.len();
        let rows = CertRows::from_ops(&vc.ops, vc.own, &vc.deps);
        for op in &vc.ops {
            let Op::Rela { rel, args } = op else {
                continue;
            };
            let chid = match rel {
                geolog_envelope::ElemRef::External { dep_index, counter } => {
                    let Some(rev) = vc.deps.get(*dep_index as usize) else {
                        return Err(format!("claim rel dep_index {dep_index} out of range"));
                    };
                    (*rev, *counter)
                }
                other => {
                    return Err(format!("claim rel ref not external: {other:?}"));
                }
            };
            let Some(name) = kit.claim_chids.get(&chid) else {
                // A relation row outside the side-condition roster
                // (e.g. membership data) is content, not a claim.
                continue;
            };
            claim_rows += 1;
            let Some(local) = kit.provider.local_by_name(name) else {
                return Err(format!(
                    "claim relation `{name}` is declared by the baked revision but not \
                     claimed by this provider build — undischargeable, refusing"
                ));
            };
            let cells: Vec<Vec<u8>> = args.iter().map(enc_val).collect();
            let refs: Vec<&[u8]> = cells.iter().map(|c| c.as_slice()).collect();
            let t = tallies.entry(name.clone()).or_default();
            match kit.provider.filter_rows(local, &refs, &rows) {
                Verdict::Holds => t.holds += 1,
                Verdict::Fails => t.fails += 1,
                Verdict::Refused(r) => t.refused.push(r),
            }
        }
    }
    if claim_rows == 0 {
        return Err(
            "no claim rows: a certificate that claims nothing certifies nothing \
             (refusing the vacuous accept)"
                .to_string(),
        );
    }
    // Roster: observed relations plus every explicitly expected name —
    // an expectation on a relation with no rows must FAIL, not vanish.
    let mut roster: Vec<String> = tallies.keys().cloned().collect();
    if let Expect::Claims(map) = expect {
        for name in map.keys() {
            if !roster.contains(name) {
                roster.push(name.clone());
            }
        }
    }
    roster.sort();
    let mut parts = Vec::new();
    let mut ok = true;
    for name in &roster {
        let t = tallies.remove(name).unwrap_or_default();
        let n = t.holds + t.fails;
        if let Some(r) = t.refused.first() {
            return Err(format!("claims `{name}` refused: {r}"));
        }
        if t.fails > 0 {
            ok = false;
        }
        if let Some(m) = expect.for_name(name) {
            if n != m || t.holds != m {
                ok = false;
            }
            parts.push(format!("{name}={}/{m}", t.holds));
        } else {
            parts.push(format!("{name}={}/{n}", t.holds));
        }
    }
    let verdict = if ok { "ACCEPT" } else { "FAIL" };
    Ok(format!(
        "{verdict} commits={} ops={total_ops} claims {}",
        commits.len(),
        parts.join(" ")
    ))
}

/// One file's row in the `--timings` receipt.
struct FileTiming {
    name: String,
    /// The file's own check wall — read/parse/classify/verify/
    /// discharge/verdict-assembly — with any first-contact baked-kit
    /// derivation excluded (that cost is per-process, reported under
    /// `kit_derivations`, and would misattribute as this file's
    /// marginal cost otherwise).
    wall_s: f64,
    verdict: &'static str,
}

/// Minimal JSON string escape (quotes, backslash, control chars).
fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

/// Serialize the timings receipt. All walls are one process-local
/// monotonic clock (`std::time::Instant`), in seconds.
fn timings_json(
    startup_s: f64,
    files: &[FileTiming],
    derivations: &[(String, f64)],
    total_wall_s: f64,
) -> String {
    let mut out = String::new();
    out.push_str("{\n \"schema\": \"maitria.glc-check.timings.v1\",\n");
    out.push_str(" \"clock\": \"monotonic, process-local, seconds\",\n");
    out.push_str(&format!(" \"startup_s\": {startup_s},\n"));
    out.push_str(" \"files\": [\n");
    for (i, f) in files.iter().enumerate() {
        out.push_str(&format!(
            "  {{\"file\": \"{}\", \"wall_s\": {}, \"verdict\": \"{}\"}}{}\n",
            json_escape(&f.name),
            f.wall_s,
            f.verdict,
            if i + 1 < files.len() { "," } else { "" }
        ));
    }
    out.push_str(" ],\n \"kit_derivations\": [\n");
    for (i, (pin, wall)) in derivations.iter().enumerate() {
        out.push_str(&format!(
            "  {{\"pin\": \"{pin}\", \"wall_s\": {wall}}}{}\n",
            if i + 1 < derivations.len() { "," } else { "" }
        ));
    }
    out.push_str(&format!(" ],\n \"total_wall_s\": {total_wall_s}\n}}\n"));
    out
}

fn classify(c: &Container, staged_revs: &[[u8; 32]]) -> Result<Mode, String> {
    let mut fluid = false;
    let mut bl = false;
    let mut spde = false;
    let mut petri = false;
    let mut gym = 0usize;
    let mut gymrw = false;
    let mut gymeproc = false;
    let mut baked: Option<[u8; 32]> = None;
    let mut staged: Option<[u8; 32]> = None;
    for p in &c.prereqs {
        if p.chid == FLUID_V0_REV {
            fluid = true;
        } else if p.chid == BL_STACK_V0_REV || p.chid == BL_CERT_V0_REV {
            bl = true;
        } else if p.chid == SPDE_V0_REV {
            spde = true;
        } else if p.chid == PETRI_V0_REV {
            petri = true;
        } else if p.chid == GYM_QTSL_V0_REV
            || p.chid == GYM_QTSLCERT_V0_REV
            || p.chid == GYM_DTMC_V0_REV
        {
            gym += 1;
        } else if p.chid == GYMRW_V0_REV {
            gymrw = true;
        } else if p.chid == GYMEPROC_V0_REV {
            gymeproc = true;
        } else if resolve_baked_rev(&p.chid).is_some() {
            if baked.is_some() {
                return Err(
                    "prereq_mix: multiple baked closure revisions in one container — a \
                     certificate speaks one closure's vocabulary, of one revision event"
                        .to_string(),
                );
            }
            baked = Some(p.chid);
        } else if staged_revs.contains(&p.chid) {
            if staged.is_some() {
                return Err(
                    "prereq_mix: multiple staged closure revisions in one container — a \
                     certificate speaks one closure's vocabulary"
                        .to_string(),
                );
            }
            staged = Some(p.chid);
        } else {
            return Err(format!(
                "unknown_prereq: flag {} chid {} not in this checker's roster",
                p.flag,
                hex32(&p.chid)
            ));
        }
    }
    if gym > 0 && gym < 3 {
        return Err(format!(
            "prereq_gym_partial: {gym} of the 3 staged gym revisions named — \
             the deadline walk spans Qtsl + QtslCert + Dtmc, refusing"
        ));
    }
    #[rustfmt::skip]
    let mode = match (fluid, bl, spde, petri, gym == 3, gymrw, gymeproc, baked, staged) {
        (true, false, false, false, false, false, false, None, None) => Ok(Mode::Fluid),
        (false, true, false, false, false, false, false, None, None) => Ok(Mode::Bl),
        (false, false, true, false, false, false, false, None, None) => Ok(Mode::Spde),
        (false, false, false, true, false, false, false, None, None) => Ok(Mode::Petri),
        (false, false, false, false, true, false, false, None, None) => Ok(Mode::Gym),
        (false, false, false, false, false, true, false, None, None) => Ok(Mode::GymRw),
        (false, false, false, false, false, false, true, None, None) => Ok(Mode::GymEproc),
        (false, false, false, false, false, false, false, Some(rev), None) => {
            Ok(Mode::BakedCert(rev))
        }
        (false, false, false, false, false, false, false, None, Some(rev)) => {
            Ok(Mode::StagedCert(rev))
        }
        (false, false, false, false, false, false, false, None, None) => {
            // No prerequisites at all: a self-contained theory-chain
            // container (the store extracts). The chain checker
            // refuses loudly unless a pinned baked revision is among
            // the commits.
            Ok(Mode::BakedChain)
        }
        _ => Err("prereq_mix: multiple family vocabularies in one container".to_string()),
    };
    mode
}

fn main() {
    let t_main = Instant::now();
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let mut expect = Expect::None;
    let mut require_tag: Option<&'static str> = None;
    let mut timings_path: Option<String> = None;
    let mut staged_chain_paths: Vec<String> = Vec::new();
    loop {
        match args.first().map(|s| s.as_str()) {
            Some("--gym") => {
                args.remove(0);
                require_tag = Some("gym");
            }
            Some("--gym-rw") => {
                args.remove(0);
                require_tag = Some("gym-rw");
            }
            Some("--gym-eproc") => {
                args.remove(0);
                require_tag = Some("gym-eproc");
            }
            Some("--baked-chain") => {
                args.remove(0);
                require_tag = Some("baked-chain");
            }
            Some("--baked-cert") => {
                args.remove(0);
                require_tag = Some("baked-cert");
            }
            Some("--staged-cert") => {
                args.remove(0);
                require_tag = Some("staged-cert");
            }
            Some("--staged-chain") => {
                args.remove(0);
                if args.is_empty() {
                    eprintln!("--staged-chain wants a chain .glc path");
                    std::process::exit(2);
                }
                staged_chain_paths.push(args.remove(0));
            }
            Some("--expect-modes") => {
                args.remove(0);
                let n = args.remove(0);
                expect = Expect::Modes(n.parse().unwrap_or_else(|_| {
                    eprintln!("--expect-modes wants a number, got `{n}`");
                    std::process::exit(2);
                }));
            }
            Some("--expect-claims") => {
                args.remove(0);
                let spec = args.remove(0);
                let mut map = HashMap::new();
                for part in spec.split(',') {
                    let Some((name, count)) = part.split_once('=') else {
                        eprintln!("--expect-claims wants name=N[,name=N...], got `{spec}`");
                        std::process::exit(2);
                    };
                    let n: usize = count.parse().unwrap_or_else(|_| {
                        eprintln!("--expect-claims `{name}` wants a number, got `{count}`");
                        std::process::exit(2);
                    });
                    map.insert(name.to_string(), n);
                }
                expect = Expect::Claims(map);
            }
            Some("--timings") => {
                args.remove(0);
                if args.is_empty() {
                    eprintln!("--timings wants a file path");
                    std::process::exit(2);
                }
                timings_path = Some(args.remove(0));
            }
            _ => break,
        }
    }
    if args.is_empty() {
        eprintln!(
            "usage: glc-check [--gym | --gym-rw | --gym-eproc | --baked-chain | --baked-cert | \
             --staged-cert] [--staged-chain <chain.glc>]... \
             [--expect-modes N | --expect-claims name=N,...] [--timings <file>] <file.glc>..."
        );
        std::process::exit(2);
    }

    // Staged closure kits: explicit chain containers loaded up front
    // (the `--staged-chain` lane). Derivation IS validation — a chain
    // that does not verify or derive refuses the invocation here,
    // before any certificate is read. The baked roster is untouched.
    let mut staged_kits: HashMap<[u8; 32], BakedKit> = HashMap::new();
    let mut staged_revs: Vec<[u8; 32]> = Vec::new();
    for path in &staged_chain_paths {
        let bytes = match std::fs::read(path) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("--staged-chain {path}: read: {e}");
                std::process::exit(2);
            }
        };
        match BakedKit::from_chain_bytes(&bytes) {
            Ok((rev, kit)) => {
                if staged_kits.insert(rev, kit).is_some() {
                    eprintln!(
                        "--staged-chain {path}: revision {} already loaded",
                        hex32(&rev)
                    );
                    std::process::exit(2);
                }
                staged_revs.push(rev);
            }
            Err(e) => {
                eprintln!("--staged-chain {path}: {e}");
                std::process::exit(2);
            }
        }
    }

    // Fluid provider + claim roster.
    let fluid_ix = fluid_v0();
    let fluid_vocab = QtslVocab::build(&[&fluid_ix]);
    if fluid_vocab.bl.is_none() {
        eprintln!(
            "internal: fluid BL vocabulary failed to resolve: {:?}",
            fluid_vocab.notes
        );
        std::process::exit(2);
    }
    let fluid_provider = QtslGroundProvider::new(vec![CHECKER_SEMANTICS_REV], fluid_vocab);
    let mut fluid_claims: HashMap<Chid, &'static str> = HashMap::new();
    for name in FLUID_V0_CLAIMS {
        let d = fluid_ix.fun(name).expect("claim relation declared");
        fluid_claims.insert(d.chid, name);
    }

    // BL provider + field chids.
    let (bl_stack, bl_cert) = bl_v0_indexes();
    let bl_vocab = QtslVocab::build(&[&bl_stack, &bl_cert]);
    if bl_vocab.bl.is_none() || bl_vocab.barycoord.is_none() {
        eprintln!(
            "internal: BL staged vocabulary failed to resolve: {:?}",
            bl_vocab.notes
        );
        std::process::exit(2);
    }
    let bl_provider = QtslGroundProvider::new(vec![CHECKER_SEMANTICS_REV], bl_vocab);
    let bl_fields = BlFieldChids::build();

    // SPDE moment provider + claim roster.
    let spde_ix = spde_v0();
    let spde_vocab = QtslVocab::build(&[&spde_ix]);
    if spde_vocab.spdemoment.is_none() {
        eprintln!(
            "internal: SPDE moment vocabulary failed to resolve: {:?}",
            spde_vocab.notes
        );
        std::process::exit(2);
    }
    let spde_provider = QtslGroundProvider::new(vec![CHECKER_SEMANTICS_REV], spde_vocab);
    let mut spde_claims: HashMap<Chid, &'static str> = HashMap::new();
    for name in SPDE_V0_CLAIMS {
        let d = spde_ix.fun(name).expect("claim relation declared");
        spde_claims.insert(d.chid, name);
    }

    // Gymnasium e-process provider + claim roster.
    let gymeproc_ix = gymeproc_v0();
    let gymeproc_vocab = QtslVocab::build(&[&gymeproc_ix]);
    if gymeproc_vocab.gymeproc.is_none() {
        eprintln!(
            "internal: gymnasium e-process vocabulary failed to resolve: {:?}",
            gymeproc_vocab.notes
        );
        std::process::exit(2);
    }
    let gymeproc_provider = QtslGroundProvider::new(vec![CHECKER_SEMANTICS_REV], gymeproc_vocab);
    let mut gymeproc_claims: HashMap<Chid, &'static str> = HashMap::new();
    for name in GYMEPROC_V0_CLAIMS {
        let d = gymeproc_ix.fun(name).expect("claim relation declared");
        gymeproc_claims.insert(d.chid, name);
    }

    // Petri P-invariant provider + field chids.
    let petri_ix = petri_v0();
    let petri_vocab = QtslVocab::build(&[&petri_ix]);
    if petri_vocab.bl.is_none() {
        eprintln!(
            "internal: petri BL vocabulary failed to resolve: {:?}",
            petri_vocab.notes
        );
        std::process::exit(2);
    }
    let petri_provider = QtslGroundProvider::new(vec![CHECKER_SEMANTICS_REV], petri_vocab);
    let petri_chids = PetriChids::build(&petri_ix);

    // Gym deadline-table provider (staged Qtsl/QtslCert/Dtmc slice).
    let (gym_q, gym_qc, gym_dt) = gym_v0_indexes();
    let gym_vocab = QtslVocab::build(&[&gym_q, &gym_qc, &gym_dt]);
    if gym_vocab.deadline.is_none() {
        eprintln!(
            "internal: gym staged vocabulary failed to resolve the deadline family: {:?}",
            gym_vocab.notes
        );
        std::process::exit(2);
    }
    let gym_provider = QtslGroundProvider::new(vec![CHECKER_SEMANTICS_REV], gym_vocab);
    let gym_node_sort = gym_qc
        .sort("QDeadlineTable")
        .expect("gym vocabulary declares the QDeadlineTable sort");

    // Gym reward-table provider + field chids.
    let gymrw_ix = gymrw_v0();
    let gymrw_vocab = QtslVocab::build(&[&gymrw_ix]);
    if gymrw_vocab.gymrw.is_none() {
        eprintln!(
            "internal: gymrw vocabulary failed to resolve: {:?}",
            gymrw_vocab.notes
        );
        std::process::exit(2);
    }
    let gymrw_provider = QtslGroundProvider::new(vec![CHECKER_SEMANTICS_REV], gymrw_vocab);
    let gymrw_chids = GymRwChids::build(&gymrw_ix);

    // Baked certificate kits, derived lazily from the embedded chain
    // fixtures on the first file that needs one (chain-mode files
    // derive from their OWN bytes and never touch these).
    let mut baked_kits: HashMap<[u8; 32], BakedKit> = HashMap::new();

    // Startup = the static roster builds above, measured whether or
    // not a receipt was requested (an Instant read is nanoseconds; the
    // flag only decides whether anything is written).
    let startup_s = t_main.elapsed().as_secs_f64();
    let mut timed_files: Vec<FileTiming> = Vec::new();
    let mut derivations: Vec<(String, f64)> = Vec::new();

    let mut failed = false;
    for path in &args {
        let name = std::path::Path::new(path)
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or(path);
        let mut derivation: Option<(String, f64)> = None;
        let t_file = Instant::now();
        let result = (|| -> Result<String, String> {
            let bytes = std::fs::read(path).map_err(|e| format!("read: {e}"))?;
            let c = parse_container(&bytes)?;
            let mode = classify(&c, &staged_revs)?;
            if let Mode::BakedCert(pin) = &mode {
                if !baked_kits.contains_key(pin) {
                    let t_kit = Instant::now();
                    let kit = BakedKit::build(*pin)?;
                    derivation = Some((hex32(pin), t_kit.elapsed().as_secs_f64()));
                    baked_kits.insert(*pin, kit);
                }
            }
            if let Some(tag) = require_tag {
                if mode_tag(&mode) != tag {
                    return Err(format!(
                        "mode_flag_mismatch: --{tag} demanded but the container names \
                         the {} family",
                        mode_tag(&mode)
                    ));
                }
            }
            match mode {
                Mode::Fluid => check_claim_rows(
                    &c,
                    &fluid_provider,
                    &fluid_claims,
                    &[FLUID_V0_REV],
                    &FLUID_V0_CLAIMS,
                    &expect,
                ),
                Mode::Bl => check_bl(&c, &bl_provider, &bl_fields, &expect),
                Mode::Spde => check_claim_rows(
                    &c,
                    &spde_provider,
                    &spde_claims,
                    &[SPDE_V0_REV],
                    &SPDE_V0_CLAIMS,
                    &expect,
                ),
                Mode::Petri => check_petri(&c, &petri_provider, &petri_chids, &expect),
                Mode::Gym => check_gym(&c, &gym_provider, gym_node_sort, &expect),
                Mode::GymRw => check_gymrw(&c, &gymrw_provider, &gymrw_chids, &expect),
                Mode::GymEproc => check_claim_rows(
                    &c,
                    &gymeproc_provider,
                    &gymeproc_claims,
                    &[GYMEPROC_V0_REV],
                    &GYMEPROC_V0_CLAIMS,
                    &expect,
                ),
                Mode::BakedChain => check_baked_chain(&c, &expect),
                Mode::BakedCert(pin) => {
                    let kit = baked_kits.get(&pin).expect("kit built above");
                    check_baked_cert(&c, kit, &expect)
                }
                Mode::StagedCert(rev) => {
                    let kit = staged_kits.get(&rev).expect("kit loaded at startup");
                    check_baked_cert(&c, kit, &expect)
                }
            }
        })();
        let mut wall_s = t_file.elapsed().as_secs_f64();
        if let Some((pin, d)) = derivation {
            // First contact with this closure revision: the derivation
            // is per-process cost, not this file's marginal cost.
            wall_s -= d;
            derivations.push((pin, d));
        }
        let verdict = match &result {
            Ok(line) if line.starts_with("ACCEPT") => "ACCEPT",
            Ok(_) => "FAIL",
            Err(_) => "REFUSE",
        };
        timed_files.push(FileTiming {
            name: name.to_string(),
            wall_s,
            verdict,
        });
        match result {
            Ok(line) => {
                println!("{name} {line}");
                if !line.starts_with("ACCEPT") {
                    failed = true;
                }
            }
            Err(locus) => {
                println!("{name} REFUSE {locus}");
                failed = true;
            }
        }
    }
    if let Some(tp) = &timings_path {
        let receipt = timings_json(
            startup_s,
            &timed_files,
            &derivations,
            t_main.elapsed().as_secs_f64(),
        );
        if let Err(e) = std::fs::write(tp, receipt) {
            eprintln!("--timings write {tp}: {e}");
            std::process::exit(2);
        }
    }
    std::process::exit(if failed { 1 } else { 0 });
}
