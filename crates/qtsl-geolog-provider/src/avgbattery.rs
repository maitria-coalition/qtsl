//! `qtsl_avg_battery`: the long-run-average (LRA / Cesàro) battery
//! walk — the structural stratum of the `QAvgBattery` node's
//! verification, fail-closed at the event-6 vocabulary.
//!
//! Semantic authority: the Qtsl theory's QAvgBattery block (the
//! long-run-average battery: "the certificate is the gain/bias pair of
//! the Poisson equation — gain in Q, bias gate a certificate family —
//! with drift rows carrying the constant term INSIDE each row's
//! sequent polynomial... The walk recomputes the required orientation
//! from the concluded root") and the SECTION K face semantics of the
//! QtslCert theory source: LE face — drifts certify
//! `g - r - A·h >= 0` on scope, nonnegs certify `h >= 0`, the tie
//! certifies `g <= hi`; GE face — orientations flip, the lowbound rows
//! bound the bias above (the `E[h(X_T)]/T` correction term dies), the
//! tie certifies `g >= lo`. Producer twin: mtk-catalogue
//! `avg_battery`/`AvgKit` (whose exact tie-coherence preflight this
//! walk re-derives checker-side, per the untrusted-producer /
//! trustworthy-checker split).
//!
//! # Claim status at event 6 (read this before wondering why nothing
//! # demands the relation)
//!
//! The `QAvgBattery` SCHEMA is baked (node sort + ten attributes, the
//! e6 `lowbounds` spelling), and every name this family resolves rides
//! the baked omnibus — so the family is expected CLAIMED on both baked
//! closures. The claim RELATION `qtsl_avg_battery {battery}` is NOT
//! yet declared theory-side: kind-typing and walk-demand axioms for
//! the whole Q*Battery genus are the rules-as-rows fan's material,
//! deliberately absent at this event (the theory's own SECTION K
//! note). Until the fan's mint lands the declaration
//! (`qtsl_avg_battery : {battery: QAvgBattery} -> Prop` + the
//! unconditional `chase ax/wf/avg_battery_walk` demand — the
//! QPAlwaysFromFold pattern), no closure row demands this walk; the
//! claimed entry simply never matches a declared relation, which is
//! safe by construction (an unmatched expectation binds nothing).
//!
//! # The walk (v0: the structural stratum, decided; the leaf-sequent
//! # stratum, loudly deferred)
//!
//! From the node's closure alone, in refusal-ordered arms:
//!
//! 1. **field presence + decode** — the ten attributes, all total;
//!    `gain` an exact-Q literal; the four `QProofList` spines walked
//!    (budgeted, cycle-safe). Malformation REFUSES.
//! 2. **drifts nonempty** — decided FALSE when empty (face-free, so
//!    decided before the conclusion stages can refuse — the inc-3 A-1
//!    ordering).
//! 3. **conclusion resolution** — `QAvgBattery/proof →
//!    QProof/concludes` names the judgment; the SOLE `QSat` stating
//!    that judgment supplies the paired spec (zero or two QSat rows
//!    refuse).
//! 4. **face recompute from the concluded root** — the spec must be
//!    the sole-forall-component record (any other component species
//!    refuses as a mint-side extension; zero or multiple forall
//!    components decide FALSE); the component must be
//!    `SReturnLE {hi, ret}` (face LE) or `SReturnGE {lo, ret}` (face
//!    GE) — any other former decides FALSE; `ret` must be
//!    `poAvg {o}` — any other path observable decides FALSE. The face
//!    is RECOMPUTED here, never stored on the node (the theory's own
//!    sentence).
//! 5. **arg correspondence** — the reward observable must be
//!    `oInd {arg}` with `arg` THE SAME element as `QAvgBattery/arg`
//!    (row-grain identity, the same-complex precedent); a mismatch
//!    decides FALSE. Non-indicator observables (`oPoly` rewards)
//!    REFUSE with the case named: the `arg` posture for general
//!    polynomial rewards is unpinned at this event.
//! 6. **face-keyed family demands** (walk-refused — absence is not
//!    chase-visible): LE ⇒ `nonnegs` nonempty (the `h(x_0)`-sign kill
//!    is load-bearing); GE ⇒ `lowbounds` nonempty (the bias upper
//!    bound kills the correction term). `guards` may be empty (a
//!    one-mode flow has no jumps). Violations decide FALSE.
//! 7. **exact tie coherence** — `gain <= bound` (LE) / `gain >= bound`
//!    (GE), recomputed in exact ℚ from the row's own `gain` and the
//!    concluded root's bound; a violation decides FALSE with both
//!    sides named. (The `gain` field is the walk's cross-check datum,
//!    never a second authority — the drift rows carry `g` inside
//!    their sequent polynomials, where the deferred stratum will
//!    re-meet it.)
//! 8. **the loud deferral** — everything decidable at this event
//!    having passed, the walk REFUSES rather than warranting: the
//!    leaf-sequent correspondence stratum (each drift/nonneg/lowbound
//!    row's concluded sign sequent against generator values
//!    recomputed through the `qtsl_gen_form` seam, scope coverage
//!    against the cited `QInvScope`, and the tie row's concluded
//!    sequent form) is unrealized checker-side — the generator-seam
//!    recompute does not exist in this provider yet. Refusal over
//!    guessing (the carillon R3/R4 posture: "loudly deferred while
//!    unrealized"); the arm grows the recompute when the
//!    generator-seam stratum lands. Consequently this walk NEVER
//!    returns HOLDS at v0 — fail-closed end to end.
//!
//! Decided violations surface through the provider's named-violations
//! register (design memo F-4), exactly as the markflow/wirecausality
//! families' do. No store dependency.

use crate::qq::QQ;
use crate::roster::{EntryRow, RelKind};
use crate::rowctx::{CertRows, CtorRow, RelRow};
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{ElemRef, Value};
use std::collections::HashMap;

/// The LRA-battery family's row of the claimed roster (appended LAST
/// at registration — provider.rs; every existing roster position is
/// unchanged).
pub(crate) const ENTRIES: &[EntryRow] = &[(
    "qtsl_avg_battery",
    &[("battery", "QAvgBattery")],
    RelKind::AvgBattery,
)];

/// Budgets: refusal beyond, never divergence (the P-ACYCLIC posture).
pub const AVGBATTERY_MAX_LEAVES: usize = 1 << 12;
const MAX_DECODE_STEPS: usize = 1 << 20;

// ---------------------------------------------------------------------
// Vocabulary
// ---------------------------------------------------------------------

/// The LRA-battery vocabulary, pinned at resolution (names select,
/// shapes verify, identities pin). A production index deriving a
/// different shape fails resolution — the family is then not claimed
/// (safe-fail), never mis-decoded.
#[derive(Debug, Clone)]
pub struct AvgBatteryVocab {
    // the node's ten attributes
    a_proof: Chid,
    a_gain: Chid,
    a_arg: Chid,
    a_cert: Chid,
    a_drifts: Chid,
    a_guards: Chid,
    a_lowbounds: Chid,
    a_nonnegs: Chid,
    a_tie: Chid,
    a_scope: Chid,
    // conclusion resolution
    qproof_concludes: Chid,
    qsat_judgment: Chid,
    qsat_sys: Chid,
    qsat_spec: Chid,
    // the spec record (post-grid: components are relations)
    spec_forall: Chid,
    spec_forall_spec_pos: usize,
    spec_forall_f_pos: usize,
    /// Other component species, resolved for PRESENCE ONLY — the walk
    /// refuses on any of them (v0 warrants exactly the
    /// sole-forall-component spec).
    spec_other: Vec<(&'static str, Chid, usize)>,
    // the concluded-root formers
    s_return_le: Chid,
    s_return_le_hi: usize,
    s_return_le_ret: usize,
    s_return_ge: Chid,
    s_return_ge_lo: usize,
    s_return_ge_ret: usize,
    po_avg: Chid,
    po_avg_o: usize,
    o_ind: Chid,
    o_ind_arg: usize,
    // the proof-leaf spine
    qprooflist_sort: Chid,
    qpl_nil: Chid,
    qpl_cons: Chid,
    qpl_tail_at: usize,
    // sole-resolution sorts
    forallspec_sort: Chid,
    pathobs_sort: Chid,
    stateobs_sort: Chid,
    /// Per-sort constructor rosters for the value-like sorts the walk
    /// `sole`-resolves on: sort chid → (fun chid → domain). Rosters
    /// carry OPTIONAL sibling formers where the sweep declares them,
    /// so a wrong-former component decides FALSE (informative) rather
    /// than refusing as unresolvable.
    ctors: HashMap<Chid, HashMap<Chid, DomainSig>>,
}

/// Build the LRA-battery vocabulary. `Err` → the family is not
/// claimed (C-ORACLE safe-fail; reason recorded on the provider's
/// notes).
pub fn build_avgbattery_vocab(indices: &[&TheoryIndex]) -> Result<AvgBatteryVocab, String> {
    let sort = |name: &str| -> Result<Chid, String> {
        for index in indices {
            if let Some(c) = index.sort(name) {
                return Ok(c);
            }
        }
        Err(format!("no `{name}` sort among the swept revisions"))
    };
    let attr = |name: &str, subject: Chid| -> Result<(Chid, SortKey), String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational {
                return Err(format!("`{name}` is relational, expected an attribute"));
            }
            if d.domain != DomainSig::Unary(SortKey::Elem(subject)) {
                return Err(format!(
                    "`{name}`: expected a unary domain on its subject sort"
                ));
            }
            let Some(cod) = d.codomain else {
                return Err(format!("`{name}` has no codomain"));
            };
            return Ok((d.chid, cod));
        }
        Err(format!("no `{name}` attribute among the swept revisions"))
    };
    // A record-domain constructor of the wanted codomain sort: chid +
    // fields (bytewise order — the wire argument order).
    let former = |name: &str, want_cod: Chid| -> Result<(Chid, Vec<(String, SortKey)>), String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational || d.codomain != Some(SortKey::Elem(want_cod)) {
                return Err(format!(
                    "`{name}` is not a constructor of the expected sort"
                ));
            }
            let DomainSig::Record(fields) = &d.domain else {
                return Err(format!("`{name}`: expected a record domain"));
            };
            return Ok((d.chid, fields.clone()));
        }
        Err(format!("no `{name}` constructor among the swept revisions"))
    };
    let field_at =
        |name: &str, fields: &[(String, SortKey)], field: &str| -> Result<usize, String> {
            fields
                .iter()
                .position(|(n, _)| n == field)
                .ok_or_else(|| format!("`{name}`: no `{field}` field"))
        };

    let node_sort = sort("QAvgBattery")?;

    // --- the node's ten attributes (shapes verify the e6 schema) ----
    let (a_proof, proof_cod) = attr("QAvgBattery/proof", node_sort)?;
    let SortKey::Elem(qproof_sort) = proof_cod else {
        return Err("`QAvgBattery/proof`: codomain is not an element sort".into());
    };
    let (a_gain, gain_cod) = attr("QAvgBattery/gain", node_sort)?;
    if gain_cod != SortKey::Ground(Ground::Q) {
        return Err("`QAvgBattery/gain`: codomain is not ground Q".into());
    }
    let (a_arg, arg_cod) = attr("QAvgBattery/arg", node_sort)?;
    let SortKey::Elem(statepred_sort) = arg_cod else {
        return Err("`QAvgBattery/arg`: codomain is not an element sort".into());
    };
    let (a_cert, cert_cod) = attr("QAvgBattery/cert", node_sort)?;
    if !matches!(cert_cod, SortKey::Elem(_)) {
        return Err("`QAvgBattery/cert`: codomain is not an element sort".into());
    }
    let (a_drifts, drifts_cod) = attr("QAvgBattery/drifts", node_sort)?;
    let SortKey::Elem(qprooflist_sort) = drifts_cod else {
        return Err("`QAvgBattery/drifts`: codomain is not an element sort".into());
    };
    let list_attr = |name: &str| -> Result<Chid, String> {
        let (chid, cod) = attr(name, node_sort)?;
        if cod != SortKey::Elem(qprooflist_sort) {
            return Err(format!("`{name}`: codomain is not the QProofList sort"));
        }
        Ok(chid)
    };
    let a_guards = list_attr("QAvgBattery/guards")?;
    // The e6 spelling — né `floors`; a pre-e6 index fails resolution
    // here, which is the wanted vintage gate.
    let a_lowbounds = list_attr("QAvgBattery/lowbounds")?;
    let a_nonnegs = list_attr("QAvgBattery/nonnegs")?;
    let (a_tie, tie_cod) = attr("QAvgBattery/tie", node_sort)?;
    if !matches!(tie_cod, SortKey::Elem(_)) {
        return Err("`QAvgBattery/tie`: codomain is not an element sort".into());
    }
    let (a_scope, scope_cod) = attr("QAvgBattery/scope_warrant", node_sort)?;
    if !matches!(scope_cod, SortKey::Elem(_)) {
        return Err("`QAvgBattery/scope_warrant`: codomain is not an element sort".into());
    }

    // --- conclusion resolution (the deadline/fold walks' own
    // --- resolution discipline) --------------------------------------
    let (qproof_concludes, qc_cod) = attr("QProof/concludes", qproof_sort)?;
    let SortKey::Elem(qjudgment_sort) = qc_cod else {
        return Err("`QProof/concludes`: codomain is not an element sort".into());
    };
    let mut qsat: Option<(Chid, Chid)> = None;
    for index in indices {
        let Some(d) = index.fun("QSat/judgment") else {
            continue;
        };
        if d.relational {
            return Err("`QSat/judgment` is relational, expected an attribute".into());
        }
        let DomainSig::Unary(SortKey::Elem(qs)) = d.domain else {
            return Err("`QSat/judgment`: expected a unary element domain".into());
        };
        if d.codomain != Some(SortKey::Elem(qjudgment_sort)) {
            return Err("`QSat/judgment` does not land in the judgment sort".into());
        }
        if qsat.is_some() {
            return Err("`QSat/judgment` names two distinct attributes — ambiguous".into());
        }
        qsat = Some((d.chid, qs));
    }
    let Some((qsat_judgment, qsat_sort)) = qsat else {
        return Err("no `QSat/judgment` attribute among the swept revisions".into());
    };
    let (qsat_sys, _) = attr("QSat/sys", qsat_sort)?;
    let (qsat_spec, qsp_cod) = attr("QSat/spec", qsat_sort)?;
    let SortKey::Elem(spec_sort) = qsp_cod else {
        return Err("`QSat/spec`: codomain is not an element sort".into());
    };

    // --- the spec record spelling (post-grid: components are
    // --- relations; `Spec/root` is retired) ---------------------------
    let rel = |name: &str| -> Result<(Chid, Vec<(String, SortKey)>), String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if !d.relational || d.codomain.is_some() {
                return Err(format!("`{name}` is not a Prop-valued relation"));
            }
            let DomainSig::Record(fields) = &d.domain else {
                return Err(format!("`{name}`: expected a record domain"));
            };
            return Ok((d.chid, fields.clone()));
        }
        Err(format!("no `{name}` relation among the swept revisions"))
    };
    let (spec_forall, sf_fields) = rel("spec_forall")?;
    let spec_forall_spec_pos = field_at("spec_forall", &sf_fields, "spec")?;
    if sf_fields[spec_forall_spec_pos].1 != SortKey::Elem(spec_sort) {
        return Err("`spec_forall`: `spec` field is not the Spec sort".into());
    }
    let spec_forall_f_pos = field_at("spec_forall", &sf_fields, "f")?;
    let SortKey::Elem(forallspec_sort) = sf_fields[spec_forall_f_pos].1 else {
        return Err("`spec_forall`: `f` field is not an element sort".into());
    };
    let spec_other = {
        let mut out: Vec<(&'static str, Chid, usize)> = Vec::new();
        for name in [
            "spec_exists",
            "spec_score",
            "spec_or",
            "spec_guard",
            "spec_assume",
        ] {
            let (chid, fields) = rel(name)?;
            let Some(i) = fields
                .iter()
                .position(|(n, s)| n == "spec" && *s == SortKey::Elem(spec_sort))
            else {
                return Err(format!("`{name}`: no `spec` field on the Spec sort"));
            };
            out.push((name, chid, i));
        }
        out
    };

    // --- the concluded-root formers ----------------------------------
    let (s_return_le, srle_fields) = former("SReturnLE", forallspec_sort)?;
    let s_return_le_hi = field_at("SReturnLE", &srle_fields, "hi")?;
    if srle_fields[s_return_le_hi].1 != SortKey::Ground(Ground::Q) {
        return Err("`SReturnLE`: `hi` field is not ground Q".into());
    }
    let s_return_le_ret = field_at("SReturnLE", &srle_fields, "ret")?;
    let SortKey::Elem(pathobs_sort) = srle_fields[s_return_le_ret].1 else {
        return Err("`SReturnLE`: `ret` field is not an element sort".into());
    };
    let (s_return_ge, srge_fields) = former("SReturnGE", forallspec_sort)?;
    let s_return_ge_lo = field_at("SReturnGE", &srge_fields, "lo")?;
    if srge_fields[s_return_ge_lo].1 != SortKey::Ground(Ground::Q) {
        return Err("`SReturnGE`: `lo` field is not ground Q".into());
    }
    let s_return_ge_ret = field_at("SReturnGE", &srge_fields, "ret")?;
    if srge_fields[s_return_ge_ret].1 != SortKey::Elem(pathobs_sort) {
        return Err("`SReturnGE`: `ret` field is not the PathObservable sort".into());
    }
    let (po_avg, poa_fields) = former("poAvg", pathobs_sort)?;
    let po_avg_o = field_at("poAvg", &poa_fields, "o")?;
    let SortKey::Elem(stateobs_sort) = poa_fields[po_avg_o].1 else {
        return Err("`poAvg`: `o` field is not an element sort".into());
    };
    let (o_ind, oi_fields) = former("oInd", stateobs_sort)?;
    let o_ind_arg = field_at("oInd", &oi_fields, "arg")?;
    if oi_fields[o_ind_arg].1 != SortKey::Elem(statepred_sort) {
        // shape-tie: the observable's provenance field and the node's
        // `arg` field live in one sort, or the walk's correspondence
        // check would be comparing across sorts.
        return Err("`oInd`: `arg` field is not the QAvgBattery/arg sort".into());
    }

    // --- the proof-leaf spine ------------------------------------------
    let nullary = |name: &str, want_cod: Chid| -> Result<Chid, String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational
                || d.codomain != Some(SortKey::Elem(want_cod))
                || d.domain != DomainSig::Nullary
            {
                return Err(format!(
                    "`{name}` is not a nullary constructor of the expected sort"
                ));
            }
            return Ok(d.chid);
        }
        Err(format!("no `{name}` constructor among the swept revisions"))
    };
    let qpl_nil = nullary("qplNil", qprooflist_sort)?;
    let (qpl_cons, qplc_fields) = former("qplCons", qprooflist_sort)?;
    let qpl_tail_at = field_at("qplCons", &qplc_fields, "tail")?;
    if qplc_fields[qpl_tail_at].1 != SortKey::Elem(qprooflist_sort) {
        return Err("`qplCons`: `tail` field is not the QProofList sort".into());
    }

    // --- sole-resolution rosters ---------------------------------------
    let mut ctors: HashMap<Chid, HashMap<Chid, DomainSig>> = HashMap::new();
    {
        let mut add = |sort: Chid, chid: Chid, domain: DomainSig| {
            ctors.entry(sort).or_default().insert(chid, domain);
        };
        add(
            forallspec_sort,
            s_return_le,
            DomainSig::Record(srle_fields.clone()),
        );
        add(
            forallspec_sort,
            s_return_ge,
            DomainSig::Record(srge_fields.clone()),
        );
        add(pathobs_sort, po_avg, DomainSig::Record(poa_fields.clone()));
        add(stateobs_sort, o_ind, DomainSig::Record(oi_fields.clone()));
        add(qprooflist_sort, qpl_nil, DomainSig::Nullary);
        add(
            qprooflist_sort,
            qpl_cons,
            DomainSig::Record(qplc_fields.clone()),
        );
        // OPTIONAL sibling formers: where the sweep declares them, a
        // wrong-former component resolves and decides FALSE
        // (informative); where it doesn't, the same body refuses as
        // unresolvable — fail-closed either way.
        let optional: &[(Chid, &[&str])] = &[
            (
                forallspec_sort,
                &[
                    "SInit",
                    "SProbGE",
                    "SProbLE",
                    "SRegretLE",
                    "SRateLE",
                    "SRateGE",
                    "SReturnHoledLE",
                ],
            ),
            (
                pathobs_sort,
                &["poSum", "poInt", "poDisc", "poSup", "retPath"],
            ),
            (stateobs_sort, &["oPoly", "oChan", "oGate"]),
        ];
        for (sort_chid, names) in optional {
            for name in *names {
                for index in indices {
                    let Some(d) = index.fun(name) else { continue };
                    if !d.relational && d.codomain == Some(SortKey::Elem(*sort_chid)) {
                        add(*sort_chid, d.chid, d.domain.clone());
                    }
                    break;
                }
            }
        }
    }

    Ok(AvgBatteryVocab {
        a_proof,
        a_gain,
        a_arg,
        a_cert,
        a_drifts,
        a_guards,
        a_lowbounds,
        a_nonnegs,
        a_tie,
        a_scope,
        qproof_concludes,
        qsat_judgment,
        qsat_sys,
        qsat_spec,
        spec_forall,
        spec_forall_spec_pos,
        spec_forall_f_pos,
        spec_other,
        s_return_le,
        s_return_le_hi,
        s_return_le_ret,
        s_return_ge,
        s_return_ge_lo,
        s_return_ge_ret,
        po_avg,
        po_avg_o,
        o_ind,
        o_ind_arg,
        qprooflist_sort,
        qpl_nil,
        qpl_cons,
        qpl_tail_at,
        forallspec_sort,
        pathobs_sort,
        stateobs_sort,
        ctors,
    })
}

// ---------------------------------------------------------------------
// The walk
// ---------------------------------------------------------------------

/// Three-valued walk outcome: `Ok(Ok(()))` holds — UNREACHABLE at v0
/// (the loud deferral, module doc arm 8) — `Ok(Err(why))` decided
/// false (the dispatch banks the named violation), `Err(reason)`
/// refuses.
type Out = Result<Result<(), String>, String>;

/// The recomputed face (never stored on the node; never trusted from
/// the producer).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Face {
    /// Upper bound: `SReturnLE` root; tie `gain <= hi`; nonnegs
    /// load-bearing.
    Le,
    /// Lower bound: `SReturnGE` root; tie `gain >= lo`; lowbounds
    /// load-bearing.
    Ge,
}

const NAME: &str = "qtsl_avg_battery";

struct Decoder<'a> {
    v: &'a AvgBatteryVocab,
    rows: &'a CertRows,
    steps: usize,
}

impl<'a> Decoder<'a> {
    fn step(&mut self) -> Result<(), String> {
        self.steps += 1;
        if self.steps > MAX_DECODE_STEPS {
            Err(format!(
                "`{NAME}`: decode beyond the step budget ({MAX_DECODE_STEPS}) — refusing"
            ))
        } else {
            Ok(())
        }
    }

    fn elem(&self, val: &Value) -> Result<u32, String> {
        match val {
            Value::Ref(ElemRef::Local(e)) => Ok(*e),
            _ => Err(format!(
                "`{NAME}`: expected a local element ref, found a literal or external \
                 ref — cross-commit structure is not walkable here, refusing"
            )),
        }
    }

    /// An exact-rational literal cell.
    fn q_lit(&self, val: &Value, what: &str) -> Result<QQ, String> {
        match val {
            Value::Lit(l) => QQ::from_q_literal(l).ok_or_else(|| {
                format!("`{NAME}`: {what} is not an exact-Q literal — malformed rows, refusing")
            }),
            _ => Err(format!(
                "`{NAME}`: {what} is not a literal cell — malformed rows, refusing"
            )),
        }
    }

    /// The sole producing row of `elem` among `sort`'s pinned
    /// constructor roster. Zero rows: the element is unresolvable in
    /// this body (entity or foreign) — refuse. Two: ambiguous.
    fn sole(&mut self, sort: Chid, elem: u32) -> Result<&'a CtorRow, String> {
        self.step()?;
        let Some(roster) = self.v.ctors.get(&sort) else {
            return Err(format!(
                "`{NAME}`: internal — no constructor roster for the requested sort"
            ));
        };
        let mut found: Option<&'a CtorRow> = None;
        for row in self.rows.producers(elem) {
            if !roster.contains_key(&row.fun) {
                continue;
            }
            if found.is_some() {
                return Err(format!(
                    "`{NAME}`: element {elem} is produced by two constructor rows — \
                     ambiguous (P-FUN territory), refusing"
                ));
            }
            found = Some(row);
        }
        found.ok_or_else(|| {
            format!(
                "`{NAME}`: element {elem} has no constructor row of the expected sort \
                 in this body — undecidable, refusing"
            )
        })
    }

    /// The sole attribute row `fun(subject) = v`, if any; two distinct
    /// rows refuse (functionality is admission conformance).
    fn sole_attr(
        &mut self,
        subject: u32,
        fun: Chid,
        what: &str,
    ) -> Result<Option<&'a Value>, String> {
        self.step()?;
        let mut found: Option<&'a Value> = None;
        for row in self.rows.attrs(subject) {
            if row.fun != fun || row.args.len() != 1 {
                continue;
            }
            if let Some(prev) = found {
                if *prev != row.value {
                    return Err(format!(
                        "`{NAME}`: `{what}` stated twice for element {subject} with \
                         distinct values — ambiguous, refusing"
                    ));
                }
                continue;
            }
            found = Some(&row.value);
        }
        Ok(found)
    }

    fn need_attr(&mut self, subject: u32, fun: Chid, what: &str) -> Result<&'a Value, String> {
        self.sole_attr(subject, fun, what)?.ok_or_else(|| {
            format!("`{NAME}`: node walk found no `{what}` row for element {subject} — refusing")
        })
    }

    /// Walk a `qplNil`/`qplCons` proof-leaf spine, returning its
    /// LENGTH (leaf content is the deferred stratum's business —
    /// arm 8 of the module doc).
    fn leaf_count(&mut self, head_elem: u32, what: &str) -> Result<usize, String> {
        let mut n = 0usize;
        let mut cur = head_elem;
        loop {
            self.step()?;
            let row = self.sole(self.v.qprooflist_sort, cur)?;
            if row.fun == self.v.qpl_nil {
                return Ok(n);
            }
            if row.fun != self.v.qpl_cons {
                return Err(format!(
                    "`{NAME}`: element {cur} is constructed by a fun outside the \
                     qplNil/qplCons pair — malformed rows, refusing"
                ));
            }
            let tail = row.args.get(self.v.qpl_tail_at).ok_or_else(|| {
                format!("`{NAME}`: qplCons row arity mismatch at element {cur} — refusing")
            })?;
            n += 1;
            if n > AVGBATTERY_MAX_LEAVES {
                return Err(format!(
                    "`{NAME}`: `{what}` spine beyond the leaf budget \
                     ({AVGBATTERY_MAX_LEAVES}) — refusing"
                ));
            }
            cur = self.elem(tail)?;
        }
    }

    /// Distinct relation-instance rows of `rel` whose `pos`-th
    /// argument is `subject`.
    fn distinct_rel_rows(
        &mut self,
        rel: Chid,
        pos: usize,
        subject: u32,
        what: &str,
    ) -> Result<Vec<&'a RelRow>, String> {
        self.step()?;
        let target = Value::Ref(ElemRef::Local(subject));
        let mut out: Vec<&RelRow> = Vec::new();
        for row in self.rows.rel_rows_citing(subject) {
            if row.rel != rel {
                continue;
            }
            let Some(cell) = row.args.get(pos) else {
                return Err(format!(
                    "`{NAME}`: `{what}` row arity mismatch — malformed rows, refusing"
                ));
            };
            if *cell != target {
                continue;
            }
            if out.iter().any(|r| r.args == row.args) {
                continue;
            }
            out.push(row);
        }
        Ok(out)
    }
}

impl AvgBatteryVocab {
    /// The whole walk. Argument: the battery element. See the module
    /// doc for the verdict roster (and for why HOLDS is unreachable
    /// at v0).
    pub(crate) fn eval_avg_battery(&self, refs: &[&Value], rows: &CertRows) -> Out {
        if refs.len() != 1 {
            return Err(format!("`{NAME}` expects 1 argument, got {}", refs.len()));
        }
        let mut d = Decoder {
            v: self,
            rows,
            steps: 0,
        };
        let node = d.elem(refs[0])?;

        // ---- arm 1: field presence + decode ---------------------------
        let gain_v = d.need_attr(node, self.a_gain, "QAvgBattery/gain")?.clone();
        let gain = d.q_lit(&gain_v, "`QAvgBattery/gain`")?;
        let arg_v = d.need_attr(node, self.a_arg, "QAvgBattery/arg")?.clone();
        let arg_elem = d.elem(&arg_v)?;
        let proof_v = d
            .need_attr(node, self.a_proof, "QAvgBattery/proof")?
            .clone();
        let proof = d.elem(&proof_v)?;
        // presence-grade: content is the deferred stratum's business.
        let cert_v = d.need_attr(node, self.a_cert, "QAvgBattery/cert")?.clone();
        d.elem(&cert_v)?;
        let tie_v = d.need_attr(node, self.a_tie, "QAvgBattery/tie")?.clone();
        d.elem(&tie_v)?;
        let scope_v = d
            .need_attr(node, self.a_scope, "QAvgBattery/scope_warrant")?
            .clone();
        d.elem(&scope_v)?;
        // the four proof-leaf spines (lengths; budgeted).
        let mut family_len = |attr: Chid, what: &str| -> Result<usize, String> {
            let v = d.need_attr(node, attr, what)?.clone();
            let head = d.elem(&v)?;
            d.leaf_count(head, what)
        };
        let n_drifts = family_len(self.a_drifts, "QAvgBattery/drifts")?;
        let _n_guards = family_len(self.a_guards, "QAvgBattery/guards")?;
        let n_lowbounds = family_len(self.a_lowbounds, "QAvgBattery/lowbounds")?;
        let n_nonnegs = family_len(self.a_nonnegs, "QAvgBattery/nonnegs")?;

        // ---- arm 2: drifts nonempty (face-free; decided before the
        // ---- conclusion stages can refuse — the inc-3 A-1 ordering) ---
        if n_drifts == 0 {
            return Ok(Err(
                "drifts family empty — the drift rows are the battery's load-bearing \
                 content on either face"
                    .into(),
            ));
        }

        // ---- arm 3: conclusion resolution ------------------------------
        let j_val = d.need_attr(proof, self.qproof_concludes, "QProof/concludes")?;
        let judgment = d.elem(j_val)?;
        let mut qsat: Option<u32> = None;
        for row in rows.producers(judgment) {
            if row.fun != self.qsat_judgment {
                continue;
            }
            let [subject] = row.args.as_slice() else {
                return Err(format!(
                    "`{NAME}`: QSat/judgment row arity mismatch — malformed rows, refusing"
                ));
            };
            let s = d.elem(subject)?;
            if qsat.replace(s).is_some() {
                return Err(format!(
                    "`{NAME}`: two QSat rows state the concluded judgment — ambiguous, \
                     refusing"
                ));
            }
        }
        let Some(qsat) = qsat else {
            return Err(format!(
                "`{NAME}`: no QSat states the concluded judgment — structure \
                 undecidable, refusing"
            ));
        };
        // presence-grade: subject agreement across the citation kit is
        // the deferred stratum's business.
        d.need_attr(qsat, self.qsat_sys, "QSat/sys")?;
        let spec_val = d.need_attr(qsat, self.qsat_spec, "QSat/spec")?.clone();
        let spec = d.elem(&spec_val)?;

        // ---- arm 4: face recompute from the concluded root -------------
        for (name, rel, pos) in &self.spec_other {
            if !d.distinct_rel_rows(*rel, *pos, spec, name)?.is_empty() {
                return Err(format!(
                    "`{NAME}`: the concluded spec carries a `{name}` component — \
                     record structure beyond the v0 walk; refusing (mint-side \
                     extension)"
                ));
            }
        }
        let comps: Vec<u32> = {
            let rows_f = d.distinct_rel_rows(
                self.spec_forall,
                self.spec_forall_spec_pos,
                spec,
                "spec_forall",
            )?;
            let mut out = Vec::with_capacity(rows_f.len());
            for r in &rows_f {
                out.push(d.elem(&r.args[self.spec_forall_f_pos])?);
            }
            out
        };
        let [f] = comps.as_slice() else {
            return Ok(Err(format!(
                "the concluded spec carries {} forall components — the LRA battery \
                 warrants exactly the sole-component record",
                comps.len()
            )));
        };
        let f_row = d.sole(self.forallspec_sort, *f)?;
        let (face, bound) =
            if f_row.fun == self.s_return_le {
                let hi = d.q_lit(
                    f_row.args.get(self.s_return_le_hi).ok_or_else(|| {
                        format!("`{NAME}`: SReturnLE row arity mismatch — refusing")
                    })?,
                    "`SReturnLE/hi`",
                )?;
                (Face::Le, hi)
            } else if f_row.fun == self.s_return_ge {
                let lo = d.q_lit(
                    f_row.args.get(self.s_return_ge_lo).ok_or_else(|| {
                        format!("`{NAME}`: SReturnGE row arity mismatch — refusing")
                    })?,
                    "`SReturnGE/lo`",
                )?;
                (Face::Ge, lo)
            } else {
                return Ok(Err(
                    "the concluded component's former is not SReturnLE/SReturnGE — the \
                 spec-root former is not a long-run-average return claim"
                        .into(),
                ));
            };
        let ret_cell = match face {
            Face::Le => f_row.args.get(self.s_return_le_ret),
            Face::Ge => f_row.args.get(self.s_return_ge_ret),
        }
        .ok_or_else(|| format!("`{NAME}`: SReturn row arity mismatch — refusing"))?;
        let ret = d.elem(ret_cell)?;
        let ret_row = d.sole(self.pathobs_sort, ret)?;
        if ret_row.fun != self.po_avg {
            return Ok(Err(
                "the concluded return functional is not poAvg — a non-Cesàro \
                 accumulator is not this battery's claim"
                    .into(),
            ));
        }
        let o_cell = ret_row
            .args
            .get(self.po_avg_o)
            .ok_or_else(|| format!("`{NAME}`: poAvg row arity mismatch — refusing"))?;
        let o = d.elem(o_cell)?;

        // ---- arm 5: arg correspondence ----------------------------------
        let o_row = d.sole(self.stateobs_sort, o)?;
        if o_row.fun != self.o_ind {
            return Err(format!(
                "`{NAME}`: the reward observable is outside the oInd injection — the \
                 `arg` posture for non-indicator (general polynomial) rewards is \
                 unpinned at this event; the occupancy reading is the realized \
                 fragment, refusing"
            ));
        }
        let oarg_cell = o_row
            .args
            .get(self.o_ind_arg)
            .ok_or_else(|| format!("`{NAME}`: oInd row arity mismatch — refusing"))?;
        let oarg = d.elem(oarg_cell)?;
        if oarg != arg_elem {
            return Ok(Err(format!(
                "arg correspondence: `QAvgBattery/arg` (element {arg_elem}) is not \
                 the concluded reward observable's indicator argument (element \
                 {oarg}) — row-grain identity is the correspondence"
            )));
        }

        // ---- arm 6: face-keyed family demands ---------------------------
        match face {
            Face::Le => {
                if n_nonnegs == 0 {
                    return Ok(Err(
                        "nonnegs family empty on the upper (LE) face — the h >= 0 \
                         rows kill the h(x_0) term's sign and are load-bearing"
                            .into(),
                    ));
                }
            }
            Face::Ge => {
                if n_lowbounds == 0 {
                    return Ok(Err(
                        "lowbounds family empty on the lower (GE) face — the bias \
                         upper-bound rows kill the E[h(X_T)]/T correction term and \
                         are load-bearing"
                            .into(),
                    ));
                }
            }
        }

        // ---- arm 7: exact tie coherence ---------------------------------
        let coherent = match face {
            Face::Le => gain.cmp_qq(&bound) != std::cmp::Ordering::Greater,
            Face::Ge => gain.cmp_qq(&bound) != std::cmp::Ordering::Less,
        };
        if !coherent {
            let (rel, side) = match face {
                Face::Le => ("<=", "hi"),
                Face::Ge => (">=", "lo"),
            };
            return Ok(Err(format!(
                "tie coherence: gain g = {gain:?} must satisfy g {rel} {side} = \
                 {bound:?} on this face (exact-Q recompute; the cited tie row \
                 certifies the same comparison)"
            )));
        }

        // ---- arm 8: the loud deferral -----------------------------------
        Err(format!(
            "`{NAME}`: structural stratum verified (conclusion resolution, face \
             recompute from the concluded root, arg correspondence, family \
             demands, exact tie coherence) — but the leaf-sequent correspondence \
             stratum (drift/nonneg/lowbound rows against generator values \
             recomputed through the qtsl_gen_form seam, scope coverage against \
             the cited QInvScope, and the tie row's concluded sequent form) is \
             unrealized checker-side; refusing rather than warranting (loud \
             deferral — this arm grows the recompute when the generator-seam \
             stratum lands)"
        ))
    }
}
