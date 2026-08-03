//! `qtsl_deadline_table`: the exact finite-horizon deadline-table walk
//! (the deadline-table rule node's proof stratum).
//!
//! Semantic authority: the QtslCert theory's deadline-table block (declaration
//! comment + `qtsl_deadline_table` decl), the Dtmc frame theory +
//! DtmcBridge (`Dtmc.geolog` — kernel outcome rows, absorbing marks,
//! `kinit`, the `DPolicy`/`pact` species), and the certified-gym
//! exact-lane checker (the workshop's executable twin)
//! (`verify_exact` — the frozen spec's source, whose WF/B/S/C
//! obligations this walk recomputes verbatim at row grain). Worked
//! instance: `FrozenLakeCertEx.rows.txt` (the whole `exact_T10`
//! certificate as one commit's rows).
//!
//! From the node's closure alone:
//!
//! - `QDeadlineTable/proof → QProof/concludes` names the judgment; the
//!   sole `QSat` stating that judgment supplies `QSat/sys` and
//!   `QSat/spec`.
//! - `Spec/root` must be `SProbGE(p, PDeadline(T, goal, producerT))` —
//!   the reach-by-deadline claim P≥p[F≤T goal] — or its LE-orientation
//!   sibling `SProbLE(q, PDeadline(T, goal, producerT))` — the upper
//!   bound P̄≤q[F≤T goal], the same wall species' second orientation
//!   (the spec-atoms re-founding; `SProbGE` was `SProb` before
//!   the harmonization). `T` must be a non-negative integer
//!   rational (the discrete walk's scope); `producerT` is horizon
//!   provenance and does not change the walk.
//! - `QSat/sys`, STAGED frame: the closed loop — a `SysWire` whose
//!   inner systems are exactly two mechanism leaves — one carrying
//!   `Mech/dtmc` (the kernel model), one carrying `Mech/dpolicy` (the
//!   policy table, whose `DPolicy/dtmc` must be the SAME element as
//!   the kernel model — row-grain identity, the same-complex
//!   precedent). The wiring is navigation only: its correctness rides
//!   `WiringMatch`/`qtsl_sys_causal`, never this walk.
//! - `QSat/sys`, CHAIN frame (the baked dc closure): a bare `SysMech`
//!   leaf whose mechanism carries chain content via the RELATIONAL
//!   `mech_dtmc {mech, chain}` bridge — the chain IS the closed law,
//!   nothing composes. The walk consumes it through the synthetic
//!   one-action view (every group at action 0, a total policy), so the
//!   obligation core below is shared verbatim between the frames.
//! - The kernel, STAGED: `DState`/`DAct` rows of the model,
//!   `DState/idx` and `DAct/idx` dense bijections onto
//!   `0..ns-1`/`0..na-1`; `kprob`
//!   outcome rows `(src, act, dst, rew) → p` merged over rewards
//!   (the reward-valued key is the kernel's own grain — the same
//!   destination legitimately appears at two rewards); absorbing
//!   self-loops are DETERMINED from `DState/absorbing` marks, never
//!   stored (a stored outcome or policy row at an absorbing source
//!   refuses — it contradicts the frame's denial axioms).
//! - The kernel, CHAIN: `dprob {src, dst} → Q` rows (parallel edges
//!   unrepresentable — a duplicated pair refuses), `dinit {chain,
//!   state} → Q` initial rows; NO absorbing marks (an absorbing state
//!   is its stored self-loop row at one — the frame's own schema
//!   decision), and a state with no outgoing rows FAILS the step
//!   obligation: the walk demands the whole law, never a
//!   substochastic fragment.
//! - The goal set: the goal `StateF` evaluated pointwise at
//!   `x0 := DState/idx` over the base fragment
//!   {`STrue`, `SFalse`, `SAtomLE`, `SAtomGE`, `SAnd`, `SOr`, `SNot`}
//!   in exact ℚ; nested `SProb` (nonbase content) refuses — it has no
//!   pointwise reading.
//! - The table: `QDeadlineTable/table`, a flat `(T+1) × ns` `QRatList`,
//!   t-major state-minor (`V_t(s) = table[t·ns + s]`; cons order =
//!   reading order).
//!
//! The obligations, verbatim from the twin (decided content —
//! violations are `Ok(false)`), stated for the GE face; the LE face
//! runs the SAME table in the super-solution direction (every
//! inequality on `V` flips, and the on-goal rows gain the explicit
//! floor the GE range pass made implicit):
//!
//! - **(WF)** every present kernel group's probabilities lie in
//!   (0, 1] and sum to exactly 1; `kinit` masses lie in (0, 1] and
//!   sum to exactly 1 (the aggregation-seam obligation, needed for
//!   (C)'s init mixture — the twin's single-init case is the point
//!   mass); the policy resolves at every needed `(s, t)`. (Both
//!   faces.)
//! - **(B)** GE: `V_T(s) ≤ [s ∈ goal]`. LE: `V_T(s) ≥ [s ∈ goal]`.
//! - **(S)** for `t < T` — GE: on goal, `V_t(s) ≤ 1` (the range
//!   pass); off goal, `V_t(s) ≤ Σ_d k(s, π_t(s), d) · V_{t+1}(d)` —
//!   with an absorbing source's determined self-loop giving
//!   `V_t(s) ≤ V_{t+1}(s)` and no policy demand. LE: on goal,
//!   `V_t(s) ≥ 1` (NOT covered by the range pass — checked
//!   explicitly); off goal, `V_t(s) ≥ Σ_d k(s, π_t(s), d) ·
//!   V_{t+1}(d)`; absorbing, `V_t(s) ≥ V_{t+1}(s)`.
//! - **(C)** every entry in [0, 1] (both faces), and — GE:
//!   `p ≤ Σ_s kinit(s) · V_0(s)` (sub-solution soundness: backward
//!   induction gives `V_t(s) ≤ P[hit goal by T | X_t = s]` pointwise,
//!   and the mixture bound concludes the claim under `X_0 ~ kinit`);
//!   LE: `Σ_s kinit(s) · V_0(s) ≤ q` (super-solution soundness:
//!   the flipped induction gives `V_t(s) ≥ P[hit goal by T | X_t =
//!   s]` pointwise — on the closed loop the upper probability IS the
//!   probability — and the mixture concludes `P̄ ≤ q`). An EXACT
//!   table satisfies every inequality of both faces with equality,
//!   which is why one table discharges either orientation (the
//!   spec-atoms memo §5; exact_T5's `SProbLE(0, PDeadline(5, goal))`
//!   is the worked boundary instance, q = 0 inside the LE face's
//!   canonical interval [0, 1)).
//!
//! Row-grain divergences from the twin, named: the twin's
//! "destinations in range" is satisfied by construction here
//! (destinations are `DState` elements of the model); an outcome or
//! choice row citing an element OUTSIDE the model's decoded alphabet
//! is identity-territory the row context cannot decide — refusal,
//! never a guessed verdict.
//!
//! Verdict discipline (the CtxArg pattern, inherited verbatim from
//! [`crate::bagcanon`]): decided violations of the obligations above
//! are `Ok(false)`; anything the row context cannot decide
//! (unconstructed/ambiguous elements, absent load-bearing attributes,
//! non-dense index families, cross-model references, non-integer
//! deadlines, nonbase goal content, stored rows at absorbing sources,
//! exhausted budgets) REFUSES, never guesses.

use crate::error::EvalError;
use crate::qq::QQ;
use crate::roster::{EntryRow, RelKind};
use crate::rowctx::CertRows;
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use std::collections::{HashMap, HashSet};

/// The fn-pointer flavor of [`crate::theory::FieldPred`] (the probes
/// here capture nothing).
type FnFieldPred<'a> = (&'a str, fn(&SortKey) -> bool);

/// The deadline-table family's row of the claimed roster (concatenated
/// at registration — provider.rs).
pub(crate) const ENTRIES: &[EntryRow] = &[(
    "qtsl_deadline_table",
    &[("node", "QDeadlineTable")],
    RelKind::Deadline,
)];

/// Budgets: refusal beyond, never divergence (the P-ACYCLIC posture).
pub const DEADLINE_MAX_STATES: usize = 1 << 16;
pub const DEADLINE_MAX_ACTS: usize = 1 << 12;
pub const DEADLINE_MAX_CELLS: usize = 1 << 22;
const MAX_DECODE_STEPS: usize = 1 << 22;

// ---------------------------------------------------------------------
// Vocabulary
// ---------------------------------------------------------------------

/// Field positions of a record-domain fun, resolved BY NAME at
/// vocabulary build (never assumed positional): the stored row order is
/// whatever the declaration's wire order is, and the walk reads each
/// field through this map.
#[derive(Debug, Clone)]
struct FieldPos(Vec<(String, usize)>);

impl FieldPos {
    fn of(&self, name: &str) -> usize {
        self.0
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, i)| *i)
            .expect("field positions verified at vocabulary build")
    }
}

/// The staged Dtmc frame + bridge (the three-revision chain this
/// corpus was first sealed against): action-keyed kernel rows, a
/// policy mechanism, absorbing MARKS with the self-loops determined.
#[derive(Debug, Clone)]
pub(crate) struct StagedDtmc {
    mech_dtmc: Chid,
    mech_dpolicy: Chid,
    dstate_dtmc: Chid,
    dstate_idx: Chid,
    dstate_absorbing: Chid,
    dact_dtmc: Chid,
    dact_idx: Chid,
    dpolicy_dtmc: Chid,
    kprob: Chid,
    kprob_pos: FieldPos,
    kinit: Chid,
    kinit_pos: FieldPos,
    pact: Chid,
    pact_pos: FieldPos,
}

/// The baked Dtmc frame (the chain species): a pure one-step law —
/// `dprob {src, dst} → Q` outcome rows, `dinit {chain, state} → Q`
/// initial rows, chain content on a mechanism via the RELATIONAL
/// `mech_dtmc {mech, chain}`. No action/policy layer (the decision
/// former is a sibling species), no absorbing mark (an absorbing state
/// is its explicit self-loop row at probability one — the theory's own
/// schema decision).
#[derive(Debug, Clone)]
pub(crate) struct ChainDtmc {
    mech_dtmc: Chid,
    mech_dtmc_pos: FieldPos,
    dstate_dtmc: Chid,
    dstate_idx: Chid,
    dprob: Chid,
    dprob_pos: FieldPos,
    dinit: Chid,
    dinit_pos: FieldPos,
}

/// Which Dtmc frame the swept revisions speak. Selection is by the
/// kernel row species' NAME (`kprob` = staged, `dprob` = chain) — the
/// two frames never coexist in one revision set, and everything
/// outside the Dtmc side (node, judgment, spec formers, table) is
/// shared.
#[derive(Debug, Clone)]
// One value per vocabulary resolution, held for the provider's
// lifetime — boxing the wide variant would buy nothing measurable.
#[allow(clippy::large_enum_variant)]
pub(crate) enum DtmcSide {
    Staged(StagedDtmc),
    Chain(ChainDtmc),
}

/// The deadline-table vocabulary, pinned at vocabulary resolution
/// (names select, shapes verify, identities pin — the
/// `build_bagcanon_vocab` pattern). Spans either the three staged
/// revisions (QtslCert nodes, Qtsl spec formers, the Dtmc frame +
/// bridge with kernel + policy) or the baked dc closure (the same
/// node/spec species after the fold, with the chain-species Dtmc
/// frame).
/// Which spec spelling the swept closure carries (the dual-pin
/// discipline: per-closure resolution keeps both vintages checking —
/// legacy event-3 containers resolve `Spec/root`, event-4 containers
/// resolve the record re-sort's component relations).
#[derive(Debug, Clone)]
enum SpecSpelling {
    /// Legacy: the root attribute; prob faces are StateF constructors.
    Root { spec_root: Chid },
    /// Post-grid: `spec_forall {f, spec}` carries the face; the other
    /// component species (exists/score/or/guard/assume) REFUSE — the
    /// deadline walk warrants exactly the sole-forall-component spec.
    Record {
        spec_forall: Chid,
        spec_forall_pos: FieldPos,
        others: Vec<(&'static str, Chid, usize)>,
    },
}

#[derive(Debug, Clone)]
pub struct DeadlineVocab {
    // QtslCert side
    node_sort: Chid,
    node_proof: Chid,
    node_table: Chid,
    qproof_concludes: Chid,
    qsat_judgment: Chid,
    qsat_sys: Chid,
    qsat_spec: Chid,
    qrl_nil: Chid,
    qrl_cons: Chid,
    ratlist_sort: Chid,
    // Qtsl side: spec formers + Poly + System constructors
    spelling: SpecSpelling,
    /// The sort the concluded face element inhabits: StateF on legacy
    /// closures (the root IS a state formula), ForallSpec post-grid.
    face_sort: Chid,
    statef_sort: Chid,
    pathf_sort: Chid,
    statef_list_sort: Chid,
    poly_sort: Chid,
    /// Post-grid only: the `oPoly` injection (atoms carry a
    /// StateObservable argument; the polynomial rides the injection).
    o_poly: Option<Chid>,
    stateobs_sort: Option<Chid>,
    s_prob_ge: Chid,
    s_prob_ge_pos: FieldPos,
    s_prob_le: Chid,
    s_prob_le_pos: FieldPos,
    p_deadline: Chid,
    s_true: Chid,
    s_false: Chid,
    s_atom_le: Chid,
    s_atom_ge: Chid,
    s_and: Chid,
    s_or: Chid,
    s_not: Chid,
    sl_nil: Chid,
    sl_cons: Chid,
    p_zero: Chid,
    p_term: Chid,
    system_sort: Chid,
    syslist_sort: Chid,
    sys_mech: Chid,
    sys_wire: Chid,
    sy_nil: Chid,
    sy_cons: Chid,
    // Dtmc frame: staged (kernel + policy + marks) or chain (dprob/dinit)
    dtmc: DtmcSide,
    /// Per-sort constructor rosters for the value-like sorts the walks
    /// `sole`-resolve on: sort chid → (fun chid → domain).
    ctors: HashMap<Chid, HashMap<Chid, DomainSig>>,
}

/// Build the deadline-table vocabulary for the named `QDeadlineTable`
/// sort. `Err` → the family is not claimed (C-ORACLE safe-fail; reason
/// recorded on the provider's vocabulary notes).
pub fn build_deadline_vocab(
    indices: &[&TheoryIndex],
    node_sort: Chid,
) -> Result<DeadlineVocab, String> {
    // An attribute: name + expected subject sort; returns (chid,
    // codomain).
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
    let elem = |cod: SortKey, what: &str| -> Result<Chid, String> {
        match cod {
            SortKey::Elem(c) => Ok(c),
            _ => Err(format!("`{what}` does not land in an element sort")),
        }
    };
    // A constructor by name + expected codomain sort; the domain check
    // receives the fields.
    let find = |name: &str,
                want_cod: Chid,
                check: &dyn Fn(&DomainSig) -> Result<(), String>|
     -> Result<(Chid, DomainSig), String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational || d.codomain != Some(SortKey::Elem(want_cod)) {
                return Err(format!(
                    "`{name}` is not a constructor of the expected sort \
                     (wrong kind or codomain)"
                ));
            }
            check(&d.domain).map_err(|why| format!("`{name}`: {why}"))?;
            return Ok((d.chid, d.domain.clone()));
        }
        Err(format!("no `{name}` constructor among the swept revisions"))
    };
    let nullary = |s: &DomainSig| -> Result<(), String> {
        if *s == DomainSig::Nullary {
            Ok(())
        } else {
            Err("expected a nullary constructor".into())
        }
    };
    let any = |_: &DomainSig| -> Result<(), String> { Ok(()) };
    // A record-domain fun (kernel/policy/init rows): field positions
    // resolved by NAME with per-field sort checks — robust to the
    // declaration's wire order.
    let record_fun = |name: &str,
                      want: &[FnFieldPred],
                      want_cod: Option<SortKey>|
     -> Result<(Chid, FieldPos), String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational {
                return Err(format!("`{name}` is relational, expected a fun"));
            }
            if let Some(wc) = want_cod {
                if d.codomain != Some(wc) {
                    return Err(format!("`{name}` has an unexpected codomain"));
                }
            }
            let DomainSig::Record(fields) = &d.domain else {
                return Err(format!("`{name}`: expected a record domain"));
            };
            if fields.len() != want.len() {
                return Err(format!("`{name}`: expected {} fields", want.len()));
            }
            let mut pos = Vec::with_capacity(want.len());
            for (wn, wf) in want {
                let Some(i) = fields.iter().position(|(n, _)| n == wn) else {
                    return Err(format!("`{name}`: no `{wn}` field"));
                };
                if !wf(&fields[i].1) {
                    return Err(format!("`{name}`: field `{wn}` has an unexpected sort"));
                }
                pos.push((wn.to_string(), i));
            }
            return Ok((d.chid, FieldPos(pos)));
        }
        Err(format!("no `{name}` fun among the swept revisions"))
    };

    // --- QtslCert side ---------------------------------------------------
    let (node_proof, np_cod) = attr("QDeadlineTable/proof", node_sort)?;
    let qproof_sort = elem(np_cod, "QDeadlineTable/proof")?;
    let (node_table, nt_cod) = attr("QDeadlineTable/table", node_sort)?;
    let ratlist_sort = elem(nt_cod, "QDeadlineTable/table")?;
    let (qproof_concludes, qc_cod) = attr("QProof/concludes", qproof_sort)?;
    let qjudgment_sort = elem(qc_cod, "QProof/concludes")?;
    // QSat: located through its judgment attribute, so resolve the
    // attribute first and take the subject sort from its declaration.
    let mut qsat: Option<(Chid, Chid)> = None; // (QSat/judgment, QSat sort)
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
            return Err("`QSat/judgment` names two distinct attributes across the \
                        swept revisions — ambiguous, refusing to pick"
                .into());
        }
        qsat = Some((d.chid, qs));
    }
    let Some((qsat_judgment, qsat_sort)) = qsat else {
        return Err("no `QSat/judgment` attribute among the swept revisions".into());
    };
    let (qsat_sys, qs_cod) = attr("QSat/sys", qsat_sort)?;
    let system_sort = elem(qs_cod, "QSat/sys")?;
    let (qsat_spec, qsp_cod) = attr("QSat/spec", qsat_sort)?;
    let spec_sort = elem(qsp_cod, "QSat/spec")?;
    let (qrl_nil, _) = find("qrlNil", ratlist_sort, &nullary)?;
    let (qrl_cons, qrl_sig) = find("qrlCons", ratlist_sort, &any)?;
    {
        let DomainSig::Record(fields) = &qrl_sig else {
            return Err("`qrlCons`: expected a record domain".into());
        };
        let ok = matches!(
            fields.as_slice(),
            [(h, SortKey::Ground(Ground::Q)), (t, SortKey::Elem(ts))]
                if h == "head" && t == "tail" && *ts == ratlist_sort
        );
        if !ok {
            return Err("`qrlCons`: expected fields (head: Q, tail: QRatList)".into());
        }
    }

    // --- Qtsl side: spec formers (dual-shape spelling) ----------------------
    // Vintage detection: a legacy closure carries `Spec/root`; the
    // event-4 grid re-sort retired it for the component relations, and
    // shipped the atoms' oPoly re-founding in the same revision — so
    // one vintage flag governs both decodes.
    let root_probe = attr("Spec/root", spec_sort);
    let (spelling, face_sort, legacy_root_cod) = match root_probe {
        Ok((spec_root, sr_cod)) => {
            let statef = elem(sr_cod, "Spec/root")?;
            (SpecSpelling::Root { spec_root }, statef, Some(statef))
        }
        Err(root_err) => {
            // The record spelling: spec_forall anchors the face sort;
            // the other component species resolve for presence only.
            let mut spec_forall: Option<(Chid, FieldPos, Chid)> = None;
            for index in indices {
                let Some(d) = index.fun("spec_forall") else {
                    continue;
                };
                if !d.relational || d.codomain.is_some() {
                    return Err("`spec_forall` is not a Prop-valued relation".into());
                }
                let DomainSig::Record(fields) = &d.domain else {
                    return Err("`spec_forall`: expected a record domain".into());
                };
                let Some(spec_i) = fields
                    .iter()
                    .position(|(n, s)| n == "spec" && *s == SortKey::Elem(spec_sort))
                else {
                    return Err("`spec_forall`: no `spec` field on the Spec sort".into());
                };
                let Some((f_i, fs)) =
                    fields
                        .iter()
                        .enumerate()
                        .find_map(|(i, (n, s))| match (n.as_str(), s) {
                            ("f", SortKey::Elem(c)) => Some((i, *c)),
                            _ => None,
                        })
                else {
                    return Err("`spec_forall`: no elem-sorted `f` field".into());
                };
                spec_forall = Some((
                    d.chid,
                    FieldPos(vec![("spec".to_string(), spec_i), ("f".to_string(), f_i)]),
                    fs,
                ));
                break;
            }
            let Some((spec_forall, spec_forall_pos, forallspec_sort)) = spec_forall else {
                return Err(format!(
                    "neither spec spelling resolved (legacy `Spec/root`: {root_err}; \
                     post-grid: no `spec_forall` relation among the swept revisions)"
                ));
            };
            let mut others: Vec<(&'static str, Chid, usize)> = Vec::new();
            for name in [
                "spec_exists",
                "spec_score",
                "spec_or",
                "spec_guard",
                "spec_assume",
            ] {
                let mut found = false;
                for index in indices {
                    let Some(d) = index.fun(name) else { continue };
                    let DomainSig::Record(fields) = &d.domain else {
                        return Err(format!("`{name}`: expected a record domain"));
                    };
                    let Some(i) = fields
                        .iter()
                        .position(|(n, s)| n == "spec" && *s == SortKey::Elem(spec_sort))
                    else {
                        return Err(format!("`{name}`: no `spec` field on the Spec sort"));
                    };
                    others.push((name, d.chid, i));
                    found = true;
                    break;
                }
                if !found {
                    return Err(format!("no `{name}` relation among the swept revisions"));
                }
            }
            (
                SpecSpelling::Record {
                    spec_forall,
                    spec_forall_pos,
                    others,
                },
                forallspec_sort,
                None,
            )
        }
    };
    // The probability wall species, both orientations (SProbGE was
    // `SProb` before the spec-atom harmonization): field positions
    // resolved BY NAME — the stored wire order is bytewise field order,
    // which lands the two faces on OPPOSITE argument orders (SProbGE:
    // p, path; SProbLE: path, q). Post-grid the faces are ForallSpec
    // constructors (the cap re-homing); legacy they are StateF's.
    let prob_face = |name: &str, thr: &str| -> Result<(Chid, FieldPos, Chid), String> {
        let (chid, sig) = find(name, face_sort, &any)?;
        let DomainSig::Record(fields) = &sig else {
            return Err(format!("`{name}`: expected a record domain"));
        };
        let Some(path_i) = fields
            .iter()
            .position(|(n, s)| n == "path" && matches!(s, SortKey::Elem(_)))
        else {
            return Err(format!("`{name}`: no `path: PathF` field"));
        };
        let SortKey::Elem(pf) = fields[path_i].1 else {
            unreachable!("matched Elem above")
        };
        let Some(thr_i) = fields
            .iter()
            .position(|(n, s)| n == thr && *s == SortKey::Ground(Ground::Q))
        else {
            return Err(format!("`{name}`: no `{thr}: Q` field"));
        };
        if fields.len() != 2 {
            return Err(format!("`{name}`: expected fields ({thr}: Q, path: PathF)"));
        }
        let pos = FieldPos(vec![(thr.to_string(), thr_i), ("path".to_string(), path_i)]);
        Ok((chid, pos, pf))
    };
    let (s_prob_ge, s_prob_ge_pos, pathf_sort) = prob_face("SProbGE", "p")?;
    let (s_prob_le, s_prob_le_pos, pathf_le) = prob_face("SProbLE", "q")?;
    if pathf_le != pathf_sort {
        return Err("`SProbGE`/`SProbLE` disagree on the PathF sort".into());
    }
    let (p_deadline, pd_sig) = find("PDeadline", pathf_sort, &any)?;
    // The goal-formula sort anchors on PDeadline's `arg` field in BOTH
    // vintages (legacy: identical to the root codomain, cross-checked;
    // post-grid: the only anchor, since the root attribute is retired).
    let statef_sort = {
        let DomainSig::Record(fields) = &pd_sig else {
            return Err("`PDeadline`: expected a record domain".into());
        };
        let t_ok = fields
            .iter()
            .any(|(n, s)| n == "T" && *s == SortKey::Ground(Ground::Q));
        let Some(arg_sort) = fields.iter().find_map(|(n, s)| match (n.as_str(), s) {
            ("arg", SortKey::Elem(c)) => Some(*c),
            _ => None,
        }) else {
            return Err("`PDeadline`: no elem-sorted `arg` field".into());
        };
        let prod_ok = fields
            .iter()
            .any(|(n, s)| n == "producerT" && *s == SortKey::Ground(Ground::B));
        if fields.len() != 3 || !t_ok || !prod_ok {
            return Err("`PDeadline`: expected fields (T: Q, arg: StateF, producerT: B)".into());
        }
        arg_sort
    };
    if let Some(rc) = legacy_root_cod {
        if rc != statef_sort {
            return Err("`Spec/root` and `PDeadline/arg` disagree on the StateF sort".into());
        }
    }
    let (s_true, _) = find("STrue", statef_sort, &nullary)?;
    let (s_false, _) = find("SFalse", statef_sort, &nullary)?;
    // Atoms follow the spelling vintage: direct polynomial argument on
    // legacy closures, the StateObservable + oPoly injection post-grid.
    let atom = |name: &str, field: &str| -> Result<(Chid, Chid), String> {
        let (c, sig) = find(name, statef_sort, &any)?;
        let DomainSig::Record(fields) = &sig else {
            return Err(format!("`{name}`: expected a record domain"));
        };
        let c_ok = fields
            .iter()
            .any(|(n, s)| n == "c" && *s == SortKey::Ground(Ground::Q));
        let Some((_, SortKey::Elem(ps))) = fields.iter().find(|(n, _)| n == field) else {
            return Err(format!("`{name}`: no `{field}` field"));
        };
        if fields.len() != 2 || !c_ok {
            return Err(format!("`{name}`: expected fields (c: Q, {field}: …)"));
        }
        Ok((c, *ps))
    };
    let (s_atom_le, s_atom_ge, poly_sort, o_poly, stateobs_sort) = match &spelling {
        SpecSpelling::Root { .. } => {
            let (le, poly_sort) = atom("SAtomLE", "poly")?;
            let (ge, poly_sort2) = atom("SAtomGE", "poly")?;
            if poly_sort != poly_sort2 {
                return Err("`SAtomLE`/`SAtomGE` disagree on the Poly sort".into());
            }
            (le, ge, poly_sort, None, None)
        }
        SpecSpelling::Record { .. } => {
            let (le, so) = atom("SAtomLE", "o")?;
            let (ge, so2) = atom("SAtomGE", "o")?;
            if so != so2 {
                return Err("`SAtomLE`/`SAtomGE` disagree on the observable sort".into());
            }
            let (o_poly, op_sig) = find("oPoly", so, &any)?;
            let DomainSig::Record(op_fields) = &op_sig else {
                return Err("`oPoly`: expected a record domain".into());
            };
            let Some(ps) = op_fields.iter().find_map(|(n, s)| match (n.as_str(), s) {
                ("poly", SortKey::Elem(c)) => Some(*c),
                _ => None,
            }) else {
                return Err("`oPoly`: no elem-sorted `poly` field".into());
            };
            (le, ge, ps, Some(o_poly), Some(so))
        }
    };
    let (s_and, sa_sig) = find("SAnd", statef_sort, &any)?;
    let statef_list_sort = match &sa_sig {
        DomainSig::Unary(SortKey::Elem(l)) => *l,
        _ => return Err("`SAnd`: expected a unary StateFList domain".into()),
    };
    let (s_or, so_sig) = find("SOr", statef_sort, &any)?;
    if so_sig != sa_sig {
        return Err("`SOr` disagrees with `SAnd` on the list domain".into());
    }
    let (s_not, sn_sig) = find("SNot", statef_sort, &any)?;
    if sn_sig != DomainSig::Unary(SortKey::Elem(statef_sort)) {
        return Err("`SNot`: expected a unary StateF domain".into());
    }
    let (sl_nil, _) = find("slNil", statef_list_sort, &nullary)?;
    let (sl_cons, slc_sig) = find("slCons", statef_list_sort, &any)?;
    {
        let DomainSig::Record(fields) = &slc_sig else {
            return Err("`slCons`: expected a record domain".into());
        };
        let ok = matches!(
            fields.as_slice(),
            [(h, SortKey::Elem(hs)), (t, SortKey::Elem(ts))]
                if h == "head" && t == "tail" && *hs == statef_sort && *ts == statef_list_sort
        );
        if !ok {
            return Err("`slCons`: expected fields (head: StateF, tail: StateFList)".into());
        }
    }
    let (p_zero, _) = find("pZero", poly_sort, &nullary)?;
    let (p_term, pt_sig) = find("pTerm", poly_sort, &any)?;
    {
        let DomainSig::Record(fields) = &pt_sig else {
            return Err("`pTerm`: expected a record domain".into());
        };
        let coeff_ok = fields
            .iter()
            .any(|(n, s)| n == "coeff" && *s == SortKey::Ground(Ground::Q));
        let expts_ok = fields
            .iter()
            .any(|(n, s)| n == "expts" && *s == SortKey::Ground(Ground::Shape));
        let tail_ok = fields
            .iter()
            .any(|(n, s)| n == "tail" && *s == SortKey::Elem(poly_sort));
        if fields.len() != 3 || !coeff_ok || !expts_ok || !tail_ok {
            return Err("`pTerm`: expected fields (coeff: Q, expts: Shape, tail: Poly)".into());
        }
    }

    // --- Qtsl side: System constructors ------------------------------------
    let (sys_mech, sm_sig) = find("SysMech", system_sort, &any)?;
    let mech_sort = {
        let DomainSig::Record(fields) = &sm_sig else {
            return Err("`SysMech`: expected a record domain".into());
        };
        let [(m, SortKey::Elem(ms))] = fields.as_slice() else {
            return Err("`SysMech`: expected fields (mech: Mech)".into());
        };
        if m != "mech" {
            return Err("`SysMech`: expected fields (mech: Mech)".into());
        }
        *ms
    };
    let (sys_wire, sw_sig) = find("SysWire", system_sort, &any)?;
    let syslist_sort = {
        let DomainSig::Record(fields) = &sw_sig else {
            return Err("`SysWire`: expected a record domain".into());
        };
        let Some((_, SortKey::Elem(sl))) = fields.iter().find(|(n, _)| n == "inner") else {
            return Err("`SysWire`: no `inner: SystemList` field".into());
        };
        if fields.len() != 2 {
            return Err("`SysWire`: expected fields (inner, wiring)".into());
        }
        *sl
    };
    let (sy_nil, _) = find("syNil", syslist_sort, &nullary)?;
    let (sy_cons, syc_sig) = find("syCons", syslist_sort, &any)?;
    {
        let DomainSig::Record(fields) = &syc_sig else {
            return Err("`syCons`: expected a record domain".into());
        };
        let ok = matches!(
            fields.as_slice(),
            [(h, SortKey::Elem(hs)), (t, SortKey::Elem(ts))]
                if h == "head" && t == "tail" && *hs == system_sort && *ts == syslist_sort
        );
        if !ok {
            return Err("`syCons`: expected fields (head: System, tail: SystemList)".into());
        }
    }

    // --- Dtmc frame: staged bridge or the baked chain species ----------------
    // Selection by the kernel row species' name: `kprob` = the staged
    // three-revision frame (action-keyed kernel, policy mechanism,
    // absorbing marks); `dprob` = the baked chain frame (pure one-step
    // law; no action layer, no marks). The two never coexist.
    let has_fun = |name: &str| indices.iter().any(|ix| ix.fun(name).is_some());
    // DState (and staged DAct): resolved through their model attributes.
    let dstate_of = |name: &str, want_cod: Chid| -> Result<(Chid, Chid), String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational {
                return Err(format!("`{name}` is relational, expected an attribute"));
            }
            let DomainSig::Unary(SortKey::Elem(subject)) = d.domain else {
                return Err(format!("`{name}`: expected a unary element domain"));
            };
            if d.codomain != Some(SortKey::Elem(want_cod)) {
                return Err(format!("`{name}` does not land in the model sort"));
            }
            return Ok((d.chid, subject));
        }
        Err(format!("no `{name}` attribute among the swept revisions"))
    };
    let is_q = |s: &SortKey| *s == SortKey::Ground(Ground::Q);
    let is_nat = |s: &SortKey| *s == SortKey::Ground(Ground::Nat);
    let dtmc = if has_fun("kprob") {
        let (mech_dtmc, md_cod) = attr("Mech/dtmc", mech_sort)?;
        let dtmc_sort = elem(md_cod, "Mech/dtmc")?;
        let (mech_dpolicy, mp_cod) = attr("Mech/dpolicy", mech_sort)?;
        let dpolicy_sort = elem(mp_cod, "Mech/dpolicy")?;
        let (dstate_dtmc, dstate_sort) = dstate_of("DState/dtmc", dtmc_sort)?;
        let (dact_dtmc, dact_sort) = dstate_of("DAct/dtmc", dtmc_sort)?;
        let (dstate_idx, di_cod) = attr("DState/idx", dstate_sort)?;
        if di_cod != SortKey::Ground(Ground::Nat) {
            return Err("`DState/idx` does not land in Nat".into());
        }
        let (dact_idx, ai_cod) = attr("DAct/idx", dact_sort)?;
        if ai_cod != SortKey::Ground(Ground::Nat) {
            return Err("`DAct/idx` does not land in Nat".into());
        }
        // The absorbing mark is a RELATION (Prop-valued): rela rows.
        let mut absorbing: Option<Chid> = None;
        for index in indices {
            let Some(d) = index.fun("DState/absorbing") else {
                continue;
            };
            if !d.relational {
                return Err("`DState/absorbing` is not relational".into());
            }
            if d.domain != DomainSig::Unary(SortKey::Elem(dstate_sort)) {
                return Err("`DState/absorbing`: expected a unary DState domain".into());
            }
            if absorbing.is_some() {
                return Err("`DState/absorbing` names two distinct relations across \
                            the swept revisions — ambiguous, refusing to pick"
                    .into());
            }
            absorbing = Some(d.chid);
        }
        let Some(dstate_absorbing) = absorbing else {
            return Err("no `DState/absorbing` relation among the swept revisions".into());
        };
        let (dpolicy_dtmc, pd_cod) = attr("DPolicy/dtmc", dpolicy_sort)?;
        if pd_cod != SortKey::Elem(dtmc_sort) {
            return Err("`DPolicy/dtmc` does not land in the model sort".into());
        }
        let (kprob, kprob_pos) = record_fun(
            "kprob",
            &[
                ("src", |s| matches!(s, SortKey::Elem(_))),
                ("act", |s| matches!(s, SortKey::Elem(_))),
                ("dst", |s| matches!(s, SortKey::Elem(_))),
                ("rew", is_q),
            ],
            Some(SortKey::Ground(Ground::Q)),
        )?;
        let (kinit, kinit_pos) = record_fun(
            "kinit",
            &[
                ("dtmc", |s| matches!(s, SortKey::Elem(_))),
                ("state", |s| matches!(s, SortKey::Elem(_))),
            ],
            Some(SortKey::Ground(Ground::Q)),
        )?;
        let (pact, pact_pos) = record_fun(
            "pact",
            &[
                ("pol", |s| matches!(s, SortKey::Elem(_))),
                ("src", |s| matches!(s, SortKey::Elem(_))),
                ("t", is_nat),
            ],
            Some(SortKey::Elem(dact_sort)),
        )?;
        DtmcSide::Staged(StagedDtmc {
            mech_dtmc,
            mech_dpolicy,
            dstate_dtmc,
            dstate_idx,
            dstate_absorbing,
            dact_dtmc,
            dact_idx,
            dpolicy_dtmc,
            kprob,
            kprob_pos,
            kinit,
            kinit_pos,
            pact,
            pact_pos,
        })
    } else if has_fun("dprob") {
        // Chain content on a mechanism is the RELATIONAL bridge
        // `mech_dtmc {mech, chain}`; the model sort comes from its
        // `chain` field.
        let mut found: Option<(Chid, FieldPos, Chid)> = None;
        for index in indices {
            let Some(d) = index.fun("mech_dtmc") else {
                continue;
            };
            if !d.relational {
                return Err("`mech_dtmc` is not relational".into());
            }
            let DomainSig::Record(fields) = &d.domain else {
                return Err("`mech_dtmc`: expected a record domain".into());
            };
            let Some(mech_i) = fields
                .iter()
                .position(|(n, s)| n == "mech" && *s == SortKey::Elem(mech_sort))
            else {
                return Err("`mech_dtmc`: no `mech: Mech` field".into());
            };
            let Some(chain_i) = fields
                .iter()
                .position(|(n, s)| n == "chain" && matches!(s, SortKey::Elem(_)))
            else {
                return Err("`mech_dtmc`: no `chain` element field".into());
            };
            if fields.len() != 2 {
                return Err("`mech_dtmc`: expected fields (chain, mech)".into());
            }
            let SortKey::Elem(dtmc_sort) = fields[chain_i].1 else {
                unreachable!("matched Elem above")
            };
            if found.is_some() {
                return Err("`mech_dtmc` names two distinct relations across the \
                            swept revisions — ambiguous, refusing to pick"
                    .into());
            }
            found = Some((
                d.chid,
                FieldPos(vec![
                    ("mech".to_string(), mech_i),
                    ("chain".to_string(), chain_i),
                ]),
                dtmc_sort,
            ));
        }
        let Some((mech_dtmc, mech_dtmc_pos, dtmc_sort)) = found else {
            return Err("no `mech_dtmc` relation among the swept revisions".into());
        };
        let (dstate_dtmc, dstate_sort) = dstate_of("DState/dtmc", dtmc_sort)?;
        let (dstate_idx, di_cod) = attr("DState/idx", dstate_sort)?;
        if di_cod != SortKey::Ground(Ground::Nat) {
            return Err("`DState/idx` does not land in Nat".into());
        }
        let (dprob, dprob_pos) = record_fun(
            "dprob",
            &[
                ("src", |s| matches!(s, SortKey::Elem(_))),
                ("dst", |s| matches!(s, SortKey::Elem(_))),
            ],
            Some(SortKey::Ground(Ground::Q)),
        )?;
        let (dinit, dinit_pos) = record_fun(
            "dinit",
            &[
                ("chain", |s| matches!(s, SortKey::Elem(_))),
                ("state", |s| matches!(s, SortKey::Elem(_))),
            ],
            Some(SortKey::Ground(Ground::Q)),
        )?;
        DtmcSide::Chain(ChainDtmc {
            mech_dtmc,
            mech_dtmc_pos,
            dstate_dtmc,
            dstate_idx,
            dprob,
            dprob_pos,
            dinit,
            dinit_pos,
        })
    } else {
        return Err(
            "no `kprob` (staged Dtmc bridge) and no `dprob` (chain species) among \
             the swept revisions — no kernel row species to walk"
                .into(),
        );
    };

    // --- per-sort constructor rosters ---------------------------------------
    let kit_sorts = [
        ratlist_sort,
        statef_sort,
        pathf_sort,
        statef_list_sort,
        poly_sort,
        system_sort,
        syslist_sort,
        // The face sort (== statef_sort on legacy closures; the
        // ForallSpec sort post-grid — the walk `sole`-resolves the
        // concluded face element over it).
        face_sort,
    ];
    let mut ctors: HashMap<Chid, HashMap<Chid, DomainSig>> = HashMap::new();
    for s in kit_sorts {
        ctors.entry(s).or_default();
    }
    // Post-grid: the observable sort is walked too (the atoms' oPoly
    // hop `sole`-resolves over its roster).
    if let Some(so) = stateobs_sort {
        ctors.entry(so).or_default();
    }
    for index in indices {
        for decl in &index.funs {
            if decl.relational || decl.name.contains('/') {
                continue;
            }
            if let Some(SortKey::Elem(c)) = decl.codomain {
                if let Some(roster) = ctors.get_mut(&c) {
                    roster.insert(decl.chid, decl.domain.clone());
                }
            }
        }
    }

    Ok(DeadlineVocab {
        node_sort,
        node_proof,
        node_table,
        qproof_concludes,
        qsat_judgment,
        qsat_sys,
        qsat_spec,
        qrl_nil,
        qrl_cons,
        ratlist_sort,
        spelling,
        face_sort,
        statef_sort,
        pathf_sort,
        statef_list_sort,
        poly_sort,
        o_poly,
        stateobs_sort,
        s_prob_ge,
        s_prob_ge_pos,
        s_prob_le,
        s_prob_le_pos,
        p_deadline,
        s_true,
        s_false,
        s_atom_le,
        s_atom_ge,
        s_and,
        s_or,
        s_not,
        sl_nil,
        sl_cons,
        p_zero,
        p_term,
        system_sort,
        syslist_sort,
        sys_mech,
        sys_wire,
        sy_nil,
        sy_cons,
        dtmc,
        ctors,
    })
}

// ---------------------------------------------------------------------
// The pure obligation core (exposed so tests hit it directly)
// ---------------------------------------------------------------------

/// Which orientation of the probability wall species the root claim
/// asserts — the direction every table inequality runs in. `Ge` is
/// the sub-solution face (`SProbGE`, lower bound); `Le` is the
/// super-solution face (`SProbLE`, upper bound). One exact table
/// satisfies both with equality.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Face {
    Ge,
    Le,
}

/// A decoded deadline certificate at the walk's grain: everything the
/// WF/B/S/C obligations consume, in exact ℚ. Kernel groups are merged
/// over rewards (the hitting walk reads probabilities only).
#[derive(Debug, Clone)]
pub struct DeadlineCert {
    pub face: Face,
    pub deadline: usize,
    pub ns: usize,
    pub goal: Vec<bool>,
    pub absorbing: Vec<bool>,
    /// `(state, mass)` — the kinit rows, state-indexed.
    pub init: Vec<(usize, QQ)>,
    pub claim: QQ,
    /// `(src, act) → [(dst, p)]` (reward-merged; per-(dst) multiplicity
    /// legal upstream, summed here).
    pub kernel: HashMap<(usize, usize), Vec<(usize, QQ)>>,
    /// `(src, t) → act`.
    pub policy: HashMap<(usize, usize), usize>,
    /// Flat `(T+1) × ns`, t-major state-minor.
    pub table: Vec<QQ>,
}

/// A decided violation — the named reason behind an `Ok(false)`
/// verdict. Every variant is an obligation the twin checks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeadlineViolation {
    /// Kernel group `(src, act)`: a probability outside (0, 1].
    KernelProbRange { src: usize, act: usize },
    /// Kernel group `(src, act)`: probabilities do not sum to 1.
    KernelGroupSum { src: usize, act: usize },
    /// A `kinit` mass outside (0, 1], or masses not summing to 1.
    InitMass,
    /// The table is not `(T+1) × ns` flat.
    TableShape { got: usize, want: usize },
    /// A table entry outside [0, 1].
    EntryRange { t: usize, s: usize },
    /// (B): `V_T(s)` above the goal indicator.
    Boundary { s: usize },
    /// (S): no policy choice at a needed `(s, t)`.
    PolicyUnresolved { s: usize, t: usize },
    /// (S): the chosen action has no kernel group.
    NoKernelGroup { s: usize, t: usize, act: usize },
    /// (S): `V_t(s)` above the one-step expectation.
    Step { s: usize, t: usize },
    /// (C): the claim above the init mixture of `V_0`.
    Claim,
    /// (B, LE face): `V_T(s)` below the goal indicator.
    BoundaryLe { s: usize },
    /// (S, LE face): `V_t(s)` below 1 at a goal state (the on-goal
    /// floor the GE range pass never needed).
    GoalLe { s: usize, t: usize },
    /// (S, LE face): `V_t(s)` below the one-step expectation.
    StepLe { s: usize, t: usize },
    /// (C, LE face): the init mixture of `V_0` above the claimed
    /// upper bound `q`.
    ClaimLe,
}

impl std::fmt::Display for DeadlineViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DeadlineViolation::KernelProbRange { src, act } => {
                write!(f, "kernel group ({src}, {act}): probability outside (0, 1]")
            }
            DeadlineViolation::KernelGroupSum { src, act } => {
                write!(
                    f,
                    "kernel group ({src}, {act}): probabilities do not sum to 1"
                )
            }
            DeadlineViolation::InitMass => {
                write!(f, "kinit masses outside (0, 1] or not summing to 1")
            }
            DeadlineViolation::TableShape { got, want } => {
                write!(f, "table carries {got} entries against (T+1)*ns = {want}")
            }
            DeadlineViolation::EntryRange { t, s } => {
                write!(f, "V_{t}({s}) outside [0, 1]")
            }
            DeadlineViolation::Boundary { s } => {
                write!(f, "V_T({s}) above the goal indicator")
            }
            DeadlineViolation::PolicyUnresolved { s, t } => {
                write!(f, "no policy choice at state {s}, step {t}")
            }
            DeadlineViolation::NoKernelGroup { s, t, act } => {
                write!(f, "pi_{t}({s}) = {act}: no kernel group")
            }
            DeadlineViolation::Step { s, t } => {
                write!(f, "V_{t}({s}) above the one-step expectation")
            }
            DeadlineViolation::Claim => {
                write!(f, "p above the init mixture of V_0")
            }
            DeadlineViolation::BoundaryLe { s } => {
                write!(f, "V_T({s}) below the goal indicator")
            }
            DeadlineViolation::GoalLe { s, t } => {
                write!(f, "V_{t}({s}) below 1 at a goal state")
            }
            DeadlineViolation::StepLe { s, t } => {
                write!(f, "V_{t}({s}) below the one-step expectation")
            }
            DeadlineViolation::ClaimLe => {
                write!(f, "the init mixture of V_0 above the claimed upper bound q")
            }
        }
    }
}

/// The WF/B/S/C obligations on a decoded certificate — the twin's
/// `verify_exact`, transposed to the row grain (init mixture, absorbing
/// self-loops already determined by the caller's decode). Pure; the
/// row-context walk feeds it and tests hit it directly.
pub fn check_deadline(c: &DeadlineCert) -> Result<(), DeadlineViolation> {
    use std::cmp::Ordering::*;
    let one = QQ::one();
    let zero = QQ::zero();
    // Shapes.
    let want = (c.deadline + 1) * c.ns;
    if c.table.len() != want {
        return Err(DeadlineViolation::TableShape {
            got: c.table.len(),
            want,
        });
    }
    let v = |t: usize, s: usize| -> &QQ { &c.table[t * c.ns + s] };
    // Entry range ((C)'s first half).
    for t in 0..=c.deadline {
        for s in 0..c.ns {
            let x = v(t, s);
            if x.cmp_qq(&zero) == Less || x.cmp_qq(&one) == Greater {
                return Err(DeadlineViolation::EntryRange { t, s });
            }
        }
    }
    // (WF) every present kernel group.
    for ((src, act), grp) in &c.kernel {
        let mut tot = QQ::zero();
        for (_d, p) in grp {
            if p.cmp_qq(&zero) != Greater || p.cmp_qq(&one) == Greater {
                return Err(DeadlineViolation::KernelProbRange {
                    src: *src,
                    act: *act,
                });
            }
            tot = tot.add(p);
        }
        if tot.cmp_qq(&one) != Equal {
            return Err(DeadlineViolation::KernelGroupSum {
                src: *src,
                act: *act,
            });
        }
    }
    // (WF) init masses: (0, 1], summing to 1.
    let mut init_tot = QQ::zero();
    for (_s, m) in &c.init {
        if m.cmp_qq(&zero) != Greater || m.cmp_qq(&one) == Greater {
            return Err(DeadlineViolation::InitMass);
        }
        init_tot = init_tot.add(m);
    }
    if init_tot.cmp_qq(&one) != Equal {
        return Err(DeadlineViolation::InitMass);
    }
    // (B): GE — V_T(s) <= [s in goal]; LE — V_T(s) >= [s in goal].
    for s in 0..c.ns {
        let ind = if c.goal[s] { &one } else { &zero };
        match c.face {
            Face::Ge => {
                if v(c.deadline, s).cmp_qq(ind) == Greater {
                    return Err(DeadlineViolation::Boundary { s });
                }
            }
            Face::Le => {
                if v(c.deadline, s).cmp_qq(ind) == Less {
                    return Err(DeadlineViolation::BoundaryLe { s });
                }
            }
        }
    }
    // (S).
    for t in 0..c.deadline {
        for s in 0..c.ns {
            if c.goal[s] {
                match c.face {
                    // GE: V_t(s) <= 1 already enforced by the range
                    // pass.
                    Face::Ge => {}
                    // LE: the on-goal floor V_t(s) >= 1 is NOT in the
                    // range pass — checked here.
                    Face::Le => {
                        if v(t, s).cmp_qq(&one) == Less {
                            return Err(DeadlineViolation::GoalLe { s, t });
                        }
                    }
                }
                continue;
            }
            if c.absorbing[s] {
                // The determined self-loop: GE — V_t(s) <= V_{t+1}(s);
                // LE — V_t(s) >= V_{t+1}(s).
                let cmp = v(t, s).cmp_qq(v(t + 1, s));
                match c.face {
                    Face::Ge if cmp == Greater => {
                        return Err(DeadlineViolation::Step { s, t });
                    }
                    Face::Le if cmp == Less => {
                        return Err(DeadlineViolation::StepLe { s, t });
                    }
                    _ => {}
                }
                continue;
            }
            let Some(act) = c.policy.get(&(s, t)) else {
                return Err(DeadlineViolation::PolicyUnresolved { s, t });
            };
            let Some(grp) = c.kernel.get(&(s, *act)) else {
                return Err(DeadlineViolation::NoKernelGroup { s, t, act: *act });
            };
            let mut acc = QQ::zero();
            for (d, p) in grp {
                acc = acc.add(&p.mul(v(t + 1, *d)));
            }
            let cmp = v(t, s).cmp_qq(&acc);
            match c.face {
                Face::Ge if cmp == Greater => {
                    return Err(DeadlineViolation::Step { s, t });
                }
                Face::Le if cmp == Less => {
                    return Err(DeadlineViolation::StepLe { s, t });
                }
                _ => {}
            }
        }
    }
    // (C): GE — p <= sum_s kinit(s) * V_0(s); LE — the mixture <= q.
    let mut mix = QQ::zero();
    for (s, m) in &c.init {
        mix = mix.add(&m.mul(v(0, *s)));
    }
    match c.face {
        Face::Ge => {
            if c.claim.cmp_qq(&mix) == Greater {
                return Err(DeadlineViolation::Claim);
            }
        }
        Face::Le => {
            if mix.cmp_qq(&c.claim) == Greater {
                return Err(DeadlineViolation::ClaimLe);
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------
// Row-context decode + evaluation
// ---------------------------------------------------------------------

fn ctx_err(name: &str, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.into(),
        index: 0,
        why,
    }
}

struct Decoder<'a> {
    name: &'a str,
    v: &'a DeadlineVocab,
    rows: &'a CertRows,
    steps: usize,
}

impl<'a> Decoder<'a> {
    fn step(&mut self) -> Result<(), EvalError> {
        self.steps += 1;
        if self.steps > MAX_DECODE_STEPS {
            Err(ctx_err(
                self.name,
                "structural walk exhausted its node budget — pathological rows".into(),
            ))
        } else {
            Ok(())
        }
    }

    fn elem(&self, val: &Value) -> Result<u32, EvalError> {
        match val {
            Value::Ref(r) => self.rows.local(r).ok_or_else(|| {
                ctx_err(
                    self.name,
                    "External element ref — the row context is single-body (this leg)".into(),
                )
            }),
            other => Err(ctx_err(
                self.name,
                format!("expected an element ref cell, got {other:?} — malformed rows"),
            )),
        }
    }

    fn q_lit(&self, val: &Value, what: &str) -> Result<QQ, EvalError> {
        match val {
            Value::Lit(l) => QQ::from_q_literal(l).ok_or_else(|| {
                ctx_err(
                    self.name,
                    format!("`{what}` is not an exact-Q literal — malformed rows"),
                )
            }),
            _ => Err(ctx_err(
                self.name,
                format!("`{what}` is not a literal cell — malformed rows"),
            )),
        }
    }

    fn nat_lit(&self, val: &Value, what: &str) -> Result<u64, EvalError> {
        match val {
            Value::Lit(l) => match l.view() {
                LiteralView::Nat(n) => Ok(n),
                _ => Err(ctx_err(
                    self.name,
                    format!("`{what}` is not a Nat literal — malformed rows"),
                )),
            },
            _ => Err(ctx_err(
                self.name,
                format!("`{what}` is not a literal cell — malformed rows"),
            )),
        }
    }

    /// The sole rostered constructor row producing `elem` on `sort`.
    fn sole(&mut self, sort: Chid, elem: u32) -> Result<&'a crate::rowctx::CtorRow, EvalError> {
        self.step()?;
        let roster = self.v.ctors.get(&sort).expect("kit sorts rostered");
        let mut found: Option<&crate::rowctx::CtorRow> = None;
        for row in self.rows.producers(elem) {
            if !roster.contains_key(&row.fun) {
                continue;
            }
            if found.is_some() {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "element {elem} is produced by multiple constructor rows — \
                         ambiguous structure (P-FUN territory), refusing"
                    ),
                ));
            }
            found = Some(row);
        }
        found.ok_or_else(|| {
            ctx_err(
                self.name,
                format!(
                    "element {elem} has no constructor row in the context — \
                     structure undecidable"
                ),
            )
        })
    }

    /// The sole attribute row `fun(subject) = v`; `None` when absent,
    /// refusal on duplication (P-FUN posture at the attribute grain).
    fn sole_attr(
        &mut self,
        subject: u32,
        fun: Chid,
        what: &str,
    ) -> Result<Option<&'a Value>, EvalError> {
        self.step()?;
        let mut found: Option<&Value> = None;
        for row in self.rows.attrs(subject) {
            if row.fun != fun {
                continue;
            }
            if found.is_some() {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "`{what}` stated twice on element {subject} — ambiguous \
                         (P-FUN territory), refusing"
                    ),
                ));
            }
            found = Some(&row.value);
        }
        Ok(found)
    }

    /// [`Self::sole_attr`] with absence as refusal (load-bearing rows).
    fn need_attr(&mut self, subject: u32, fun: Chid, what: &str) -> Result<&'a Value, EvalError> {
        self.sole_attr(subject, fun, what)?.ok_or_else(|| {
            ctx_err(
                self.name,
                format!("element {subject} has no `{what}` row — structure undecidable"),
            )
        })
    }

    /// Walk a nil/cons list into its head cells.
    fn walk_list(
        &mut self,
        sort: Chid,
        head_elem: u32,
        nil: Chid,
        cons: Chid,
    ) -> Result<Vec<Value>, EvalError> {
        let mut out = Vec::new();
        let mut visited: HashSet<u32> = HashSet::new();
        let mut cur = head_elem;
        loop {
            if !visited.insert(cur) {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "element {cur} recurs along its own list tail (P-ACYCLIC \
                         territory) — refusing"
                    ),
                ));
            }
            let row = self.sole(sort, cur)?;
            if row.fun == nil {
                return Ok(out);
            }
            if row.fun != cons {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "element {cur} is constructed by a fun outside the expected \
                         nil/cons pair — malformed rows"
                    ),
                ));
            }
            let [head, tail] = row.args.as_slice() else {
                return Err(ctx_err(self.name, "cons row arity mismatch".into()));
            };
            out.push(head.clone());
            cur = self.elem(tail)?;
        }
    }

    /// Evaluate a stored Poly at `x0 := point` (exact ℚ). Refuses on
    /// variables beyond `x0` with positive exponent — the state-index
    /// fragment has one coordinate.
    fn eval_poly_at(&mut self, poly_elem: u32, point: &QQ) -> Result<QQ, EvalError> {
        let mut acc = QQ::zero();
        let mut visited: HashSet<u32> = HashSet::new();
        let mut cur = poly_elem;
        loop {
            if !visited.insert(cur) {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "Poly element {cur} recurs along its own tail (P-ACYCLIC \
                         territory) — refusing"
                    ),
                ));
            }
            let row = self.sole(self.v.poly_sort, cur)?;
            if row.fun == self.v.p_zero {
                return Ok(acc);
            }
            if row.fun != self.v.p_term {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "Poly element {cur} is constructed by a fun outside the \
                         expected pZero/pTerm pair — malformed rows"
                    ),
                ));
            }
            let [coeff, expts, tail] = row.args.as_slice() else {
                return Err(ctx_err(self.name, "pTerm row arity mismatch".into()));
            };
            let c = self.q_lit(coeff, "pTerm/coeff")?;
            let exps: Vec<u64> = match expts {
                Value::Lit(l) => match l.view() {
                    LiteralView::Shape(s) => s.iter().collect(),
                    _ => {
                        return Err(ctx_err(
                            self.name,
                            "`pTerm/expts` is not a Shape literal — malformed rows".into(),
                        ))
                    }
                },
                _ => {
                    return Err(ctx_err(
                        self.name,
                        "`pTerm/expts` is not a literal cell — malformed rows".into(),
                    ))
                }
            };
            if exps.iter().skip(1).any(|e| *e > 0) {
                return Err(ctx_err(
                    self.name,
                    "goal polynomial mentions a variable beyond x0 — outside the \
                     state-index fragment, refusing"
                        .into(),
                ));
            }
            let e0 = exps.first().copied().unwrap_or(0);
            if e0 > 64 {
                return Err(ctx_err(
                    self.name,
                    "goal polynomial exponent beyond the budget — refusing".into(),
                ));
            }
            let mut pow = QQ::one();
            for _ in 0..e0 {
                pow = pow.mul(point);
            }
            acc = acc.add(&c.mul(&pow));
            cur = self.elem(tail)?;
        }
    }

    /// Evaluate a base StateF pointwise at `x0 := point`. Nonbase
    /// content (`SProb`, unknown constructors) refuses.
    fn eval_goal_at(
        &mut self,
        statef_elem: u32,
        point: &QQ,
        depth: usize,
    ) -> Result<bool, EvalError> {
        use std::cmp::Ordering::*;
        if depth > 64 {
            return Err(ctx_err(
                self.name,
                "goal formula nesting beyond the depth budget — refusing".into(),
            ));
        }
        let row = self.sole(self.v.statef_sort, statef_elem)?;
        let fun = row.fun;
        if fun == self.v.s_true {
            Ok(true)
        } else if fun == self.v.s_false {
            Ok(false)
        } else if fun == self.v.s_atom_le || fun == self.v.s_atom_ge {
            let [c, arg] = row.args.as_slice() else {
                return Err(ctx_err(self.name, "atom row arity mismatch".into()));
            };
            let c = self.q_lit(c, "atom/c")?;
            let mut p = self.elem(arg)?;
            // Post-grid the atom's argument is a StateObservable; only
            // the oPoly injection has a pointwise polynomial reading.
            if let (Some(o_poly), Some(so)) = (self.v.o_poly, self.v.stateobs_sort) {
                let orow = self.sole(so, p)?;
                if orow.fun != o_poly {
                    return Err(ctx_err(
                        self.name,
                        "atom observable outside the oPoly injection — no pointwise \
                         reading in the base fragment; refusing"
                            .into(),
                    ));
                }
                let [poly_cell] = orow.args.as_slice() else {
                    return Err(ctx_err(self.name, "oPoly row arity mismatch".into()));
                };
                p = self.elem(poly_cell)?;
            }
            let val = self.eval_poly_at(p, point)?;
            Ok(if fun == self.v.s_atom_le {
                val.cmp_qq(&c) != Greater
            } else {
                val.cmp_qq(&c) != Less
            })
        } else if fun == self.v.s_and || fun == self.v.s_or {
            let [list] = row.args.as_slice() else {
                return Err(ctx_err(self.name, "junction row arity mismatch".into()));
            };
            let l = self.elem(list)?;
            let heads =
                self.walk_list(self.v.statef_list_sort, l, self.v.sl_nil, self.v.sl_cons)?;
            let conj = fun == self.v.s_and;
            let mut out = conj;
            for h in heads {
                let he = self.elem(&h)?;
                let b = self.eval_goal_at(he, point, depth + 1)?;
                if conj {
                    out = out && b;
                } else {
                    out = out || b;
                }
            }
            Ok(out)
        } else if fun == self.v.s_not {
            let [inner] = row.args.as_slice() else {
                return Err(ctx_err(self.name, "SNot row arity mismatch".into()));
            };
            let ie = self.elem(inner)?;
            Ok(!self.eval_goal_at(ie, point, depth + 1)?)
        } else if fun == self.v.s_prob_ge || fun == self.v.s_prob_le {
            Err(ctx_err(
                self.name,
                "goal formula nests a probability former (nonbase content) — no \
                 pointwise reading, refusing"
                    .into(),
            ))
        } else {
            Err(ctx_err(
                self.name,
                "goal formula uses a constructor outside the base pointwise fragment \
                 — refusing"
                    .into(),
            ))
        }
    }
}

/// The `qtsl_deadline_table` evaluation. Args in wire field order:
/// `node` (same-body element ref).
pub fn eval_deadline_table(
    name: &str,
    v: &DeadlineVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let node = d.elem(args[0])?;
    let _ = v.node_sort; // anchor pinned at build; the node is entity-like (attrs only)

    // --- proof → judgment → the sole QSat -----------------------------------
    let proof_val = d
        .need_attr(node, v.node_proof, "QDeadlineTable/proof")?
        .clone();
    let proof = d.elem(&proof_val)?;
    let j_val = d
        .need_attr(proof, v.qproof_concludes, "QProof/concludes")?
        .clone();
    let judgment = d.elem(&j_val)?;
    // Rows producing the judgment element include QSat/judgment rows
    // (their VALUE cell is the judgment); demand exactly one.
    let mut qsat: Option<u32> = None;
    for row in rows.producers(judgment) {
        if row.fun != v.qsat_judgment {
            continue;
        }
        let [subject] = row.args.as_slice() else {
            return Err(ctx_err(name, "QSat/judgment row arity mismatch".into()));
        };
        let s = d.elem(subject)?;
        if qsat.replace(s).is_some() {
            return Err(ctx_err(
                name,
                "two QSat rows state the concluded judgment — ambiguous, refusing".into(),
            ));
        }
    }
    let Some(qsat) = qsat else {
        return Err(ctx_err(
            name,
            "no QSat states the concluded judgment — structure undecidable".into(),
        ));
    };
    let sys_val = d.need_attr(qsat, v.qsat_sys, "QSat/sys")?.clone();
    let sys = d.elem(&sys_val)?;
    let spec_val = d.need_attr(qsat, v.qsat_spec, "QSat/spec")?.clone();
    let spec = d.elem(&spec_val)?;

    // --- the concluded face: SProbGE(p, PDeadline(...)) or
    // SProbLE(q, PDeadline(...)) — read per the closure's spelling
    // vintage (legacy root attribute vs the record's sole forall
    // component).
    let root = match &v.spelling {
        SpecSpelling::Root { spec_root } => {
            let root_val = d.need_attr(spec, *spec_root, "Spec/root")?.clone();
            d.elem(&root_val)?
        }
        SpecSpelling::Record {
            spec_forall,
            spec_forall_pos,
            others,
        } => {
            // Any other component species: outside the walk's scope.
            for row in d.rows.rel_rows_citing(spec) {
                for (oname, orel, opos) in others {
                    if row.rel == *orel
                        && row.args.get(*opos)
                            == Some(&Value::Ref(geolog_envelope::ElemRef::Local(spec)))
                    {
                        return Err(ctx_err(
                            name,
                            format!(
                                "the concluded spec carries a `{oname}` component — \
                                 post-grid record structure outside the deadline \
                                 walk's scope, refusing"
                            ),
                        ));
                    }
                }
            }
            let spec_pos = spec_forall_pos.of("spec");
            let f_pos = spec_forall_pos.of("f");
            let mut face_elem: Option<u32> = None;
            let mut seen: Vec<&[Value]> = Vec::new();
            for row in d.rows.rel_rows_citing(spec) {
                if row.rel != *spec_forall
                    || row.args.get(spec_pos)
                        != Some(&Value::Ref(geolog_envelope::ElemRef::Local(spec)))
                {
                    continue;
                }
                if seen.contains(&row.args.as_slice()) {
                    continue; // set semantics: byte-identical rows are one row
                }
                seen.push(&row.args);
                let f_cell = row
                    .args
                    .get(f_pos)
                    .ok_or_else(|| ctx_err(name, "`spec_forall` row arity mismatch".into()))?;
                let f = d.elem(f_cell)?;
                if face_elem.replace(f).is_some() {
                    return Err(ctx_err(
                        name,
                        "two forall components on the concluded spec — the deadline \
                         walk warrants exactly one; refusing"
                            .into(),
                    ));
                }
            }
            face_elem.ok_or_else(|| {
                ctx_err(
                    name,
                    "the concluded spec carries no `spec_forall` component — \
                     structure undecidable, refusing"
                        .into(),
                )
            })?
        }
    };
    let root_row = d.sole(v.face_sort, root)?;
    let (face, thr_name, pos) = if root_row.fun == v.s_prob_ge {
        (Face::Ge, "p", &v.s_prob_ge_pos)
    } else if root_row.fun == v.s_prob_le {
        (Face::Le, "q", &v.s_prob_le_pos)
    } else {
        return Err(ctx_err(
            name,
            "the concluded face is not an SProbGE/SProbLE claim — outside the \
             deadline walk's scope, refusing"
                .into(),
        ));
    };
    if root_row.args.len() != 2 {
        return Err(ctx_err(name, "SProbGE/SProbLE row arity mismatch".into()));
    }
    let claim = d.q_lit(&root_row.args[pos.of(thr_name)], "SProb threshold")?;
    let path = d.elem(&root_row.args[pos.of("path")])?;
    let path_row = d.sole(v.pathf_sort, path)?;
    if path_row.fun != v.p_deadline {
        return Err(ctx_err(
            name,
            "the claim's path formula is not PDeadline — outside the deadline \
             walk's scope, refusing"
                .into(),
        ));
    }
    let [t_cell, goal_cell, _producer_t] = path_row.args.as_slice() else {
        return Err(ctx_err(name, "PDeadline row arity mismatch".into()));
    };
    let t_q = d.q_lit(t_cell, "PDeadline/T")?;
    // T must be a non-negative integer rational (the discrete walk).
    use num_traits::One;
    if !t_q.is_nonneg() || !t_q.den().is_one() {
        return Err(ctx_err(
            name,
            "PDeadline/T is not a non-negative integer — outside the discrete \
             walk's scope, refusing"
                .into(),
        ));
    }
    let deadline = usize::try_from(t_q.num().magnitude().clone())
        .map_err(|_| ctx_err(name, "PDeadline/T beyond the cell budget — refusing".into()))?;
    let goal_elem = d.elem(goal_cell)?;

    // --- the model: staged closed loop, or the chain species -----------------
    let sys_row = d.sole(v.system_sort, sys)?;
    let decoded = match &v.dtmc {
        DtmcSide::Staged(sv) => decode_staged_model(&mut d, rows, v, sv, sys_row, deadline)?,
        DtmcSide::Chain(cv) => decode_chain_model(&mut d, rows, v, cv, sys_row, deadline)?,
    };
    let DecodedModel {
        ns,
        absorbing,
        init,
        kernel,
        policy,
    } = decoded;

    // --- the goal set: pointwise evaluation at x0 := idx ---------------------
    let mut goal = vec![false; ns];
    for (i, g) in goal.iter_mut().enumerate() {
        let point = QQ::from_int(i as i64);
        *g = d.eval_goal_at(goal_elem, &point, 0)?;
    }

    // --- the table ------------------------------------------------------------
    let table_val = d
        .need_attr(node, v.node_table, "QDeadlineTable/table")?
        .clone();
    let table_head = d.elem(&table_val)?;
    let cells = d.walk_list(v.ratlist_sort, table_head, v.qrl_nil, v.qrl_cons)?;
    if cells.len() > DEADLINE_MAX_CELLS {
        return Err(ctx_err(
            name,
            "table beyond the cell budget — refusing".into(),
        ));
    }
    let mut table = Vec::with_capacity(cells.len());
    for c in &cells {
        table.push(d.q_lit(c, "qrlCons/head")?);
    }

    // --- the obligations --------------------------------------------------------
    let cert = DeadlineCert {
        face,
        deadline,
        ns,
        goal,
        absorbing,
        init,
        claim,
        kernel,
        policy,
        table,
    };
    Ok(check_deadline(&cert).is_ok())
}

/// One decoded model at the walk's grain, whichever frame carried it:
/// the staged closed loop (kernel + policy mechs, absorbing marks) or
/// the chain species (dprob/dinit under the synthetic one-action view).
struct DecodedModel {
    ns: usize,
    absorbing: Vec<bool>,
    init: Vec<(usize, QQ)>,
    kernel: HashMap<(usize, usize), Vec<(usize, QQ)>>,
    policy: HashMap<(usize, usize), usize>,
}

/// Dense idx bijection over model-membership elements (`DState/idx`,
/// `DAct/idx`): every element gets exactly one index in `0..n`.
fn dense_ids(
    d: &mut Decoder,
    elems: &[u32],
    idx_fun: Chid,
    what: &str,
    out: &mut HashMap<u32, usize>,
) -> Result<(), EvalError> {
    let n = elems.len();
    let mut seen = vec![false; n];
    for e in elems {
        let iv = d.need_attr(*e, idx_fun, what)?.clone();
        let i = d.nat_lit(&iv, what)? as usize;
        if i >= n || seen[i] {
            return Err(ctx_err(
                d.name,
                format!(
                    "`{what}` values are not a dense bijection onto 0..{n} — \
                     indexed-family structure undecidable, refusing"
                ),
            ));
        }
        seen[i] = true;
        if out.insert(*e, i).is_some() {
            return Err(ctx_err(
                d.name,
                format!("duplicate membership row for one element (`{what}`) — refusing"),
            ));
        }
    }
    Ok(())
}

/// The staged closed loop: exactly one kernel mech + one policy mech
/// under a SysWire, kernel groups reward-merged, absorbing self-loops
/// determined from marks, policy rows read per (state, step).
fn decode_staged_model(
    d: &mut Decoder,
    rows: &CertRows,
    v: &DeadlineVocab,
    sv: &StagedDtmc,
    sys_row: &crate::rowctx::CtorRow,
    deadline: usize,
) -> Result<DecodedModel, EvalError> {
    let name = d.name;
    if sys_row.fun == v.sys_mech {
        return Err(ctx_err(
            name,
            "QSat/sys is a bare mechanism — the walk needs the closed loop \
             (kernel + policy composed via SysWire), refusing"
                .into(),
        ));
    }
    if sys_row.fun != v.sys_wire {
        return Err(ctx_err(
            name,
            "QSat/sys is constructed by a fun outside the expected SysMech/SysWire \
             pair — malformed rows"
                .into(),
        ));
    }
    let inner_val = match &sys_row.args[..] {
        [inner, _wiring] => inner.clone(),
        _ => return Err(ctx_err(name, "SysWire row arity mismatch".into())),
    };
    let inner = d.elem(&inner_val)?;
    let inner_systems = d.walk_list(v.syslist_sort, inner, v.sy_nil, v.sy_cons)?;
    let mut kernel_model: Option<u32> = None;
    let mut policy_table: Option<u32> = None;
    for s_val in &inner_systems {
        let s = d.elem(s_val)?;
        let row = d.sole(v.system_sort, s)?;
        if row.fun != v.sys_mech {
            return Err(ctx_err(
                name,
                "an inner system of the closed loop is not a mechanism leaf — outside \
                 the walk's scope, refusing"
                    .into(),
            ));
        }
        let [mech_cell] = row.args.as_slice() else {
            return Err(ctx_err(name, "SysMech row arity mismatch".into()));
        };
        let mech = d.elem(mech_cell)?;
        let dtmc = d.sole_attr(mech, sv.mech_dtmc, "Mech/dtmc")?.cloned();
        let dpol = d.sole_attr(mech, sv.mech_dpolicy, "Mech/dpolicy")?.cloned();
        match (dtmc, dpol) {
            (Some(_), Some(_)) => {
                return Err(ctx_err(
                    name,
                    "a mechanism carries both kernel and policy content — the \
                     exclusivity fixture's territory, refusing"
                        .into(),
                ));
            }
            (Some(k_val), None) => {
                let k = d.elem(&k_val)?;
                if kernel_model.replace(k).is_some() {
                    return Err(ctx_err(
                        name,
                        "two kernel mechanisms in the composite — outside the walk's \
                         shape, refusing"
                            .into(),
                    ));
                }
            }
            (None, Some(p_val)) => {
                let p = d.elem(&p_val)?;
                if policy_table.replace(p).is_some() {
                    return Err(ctx_err(
                        name,
                        "two policy mechanisms in the composite — outside the walk's \
                         shape, refusing"
                            .into(),
                    ));
                }
            }
            (None, None) => {
                return Err(ctx_err(
                    name,
                    "an inner mechanism carries neither kernel nor policy content — \
                     outside the walk's shape, refusing"
                        .into(),
                ));
            }
        }
    }
    let (Some(model), Some(pol)) = (kernel_model, policy_table) else {
        return Err(ctx_err(
            name,
            "the composite lacks a kernel or a policy mechanism — outside the walk's \
             shape, refusing"
                .into(),
        ));
    };
    // The policy must read the SAME model element (row-grain identity —
    // the same-complex precedent; distinct elements are chase-congruence
    // territory, not decidable here).
    let pol_model_val = d.need_attr(pol, sv.dpolicy_dtmc, "DPolicy/dtmc")?.clone();
    if d.elem(&pol_model_val)? != model {
        return Err(ctx_err(
            name,
            "DPolicy/dtmc is a different element than the kernel model — row-grain \
             identity undecidable across distinct elements, refusing"
                .into(),
        ));
    }

    // --- the model's alphabets: dense idx bijections --------------------------
    // DState/dtmc rows carry the model as their VALUE cell.
    let mut state_ids: HashMap<u32, usize> = HashMap::new();
    let mut act_ids: HashMap<u32, usize> = HashMap::new();
    {
        let mut state_elems: Vec<u32> = Vec::new();
        let mut act_elems: Vec<u32> = Vec::new();
        for row in rows.producers(model) {
            if row.fun == sv.dstate_dtmc || row.fun == sv.dact_dtmc {
                let [subject] = row.args.as_slice() else {
                    return Err(ctx_err(name, "model-membership row arity mismatch".into()));
                };
                let s = d.elem(subject)?;
                if row.fun == sv.dstate_dtmc {
                    state_elems.push(s);
                } else {
                    act_elems.push(s);
                }
            }
        }
        if state_elems.len() > DEADLINE_MAX_STATES || act_elems.len() > DEADLINE_MAX_ACTS {
            return Err(ctx_err(
                name,
                "state/action alphabet beyond the budget — refusing".into(),
            ));
        }
        dense_ids(d, &state_elems, sv.dstate_idx, "DState/idx", &mut state_ids)?;
        dense_ids(d, &act_elems, sv.dact_idx, "DAct/idx", &mut act_ids)?;
    }
    let ns = state_ids.len();
    if ns == 0 {
        return Err(ctx_err(
            name,
            "the kernel model has no states in view — structure undecidable".into(),
        ));
    }
    if (deadline + 1).saturating_mul(ns) > DEADLINE_MAX_CELLS {
        return Err(ctx_err(
            name,
            "(T+1)*ns beyond the cell budget — refusing".into(),
        ));
    }

    // Absorbing marks (relation rows on the state element).
    let mut absorbing = vec![false; ns];
    for (e, i) in &state_ids {
        for r in rows.rel_attrs(*e) {
            if r.rel == sv.dstate_absorbing {
                absorbing[*i] = true;
            }
        }
    }

    // --- kernel rows (reward-merged), init rows, policy rows -----------------
    let src_pos = sv.kprob_pos.of("src");
    let act_pos = sv.kprob_pos.of("act");
    let dst_pos = sv.kprob_pos.of("dst");
    let mut kernel: HashMap<(usize, usize), Vec<(usize, QQ)>> = HashMap::new();
    {
        // Outcome keys seen, for the P-FUN check (same (src,act,dst,rew)
        // twice = parallel outcomes; hash-consing upstream makes true
        // duplicates one row, so a repeat here is malformation).
        let mut seen: HashSet<(u32, u32, u32, Vec<u8>)> = HashSet::new();
        for (state_elem, s_idx) in &state_ids {
            for row in rows.arg_rows(*state_elem) {
                if row.fun != sv.kprob {
                    continue;
                }
                d.step()?;
                let src_elem = d.elem(&row.args[src_pos])?;
                if src_elem != *state_elem {
                    continue; // cited as dst here; the src's own sweep files it
                }
                if absorbing[*s_idx] {
                    return Err(ctx_err(
                        name,
                        "a stored outcome row at an absorbing source — the determined \
                         self-loop is structure, never data (frame denial territory), \
                         refusing"
                            .into(),
                    ));
                }
                let act_elem = d.elem(&row.args[act_pos])?;
                let Some(a_idx) = act_ids.get(&act_elem) else {
                    return Err(ctx_err(
                        name,
                        "an outcome row cites an action outside the model's decoded \
                         alphabet — identity undecidable, refusing"
                            .into(),
                    ));
                };
                let dst_elem = d.elem(&row.args[dst_pos])?;
                let Some(d_idx) = state_ids.get(&dst_elem) else {
                    return Err(ctx_err(
                        name,
                        "an outcome row cites a destination outside the model's \
                         decoded state set — identity undecidable, refusing"
                            .into(),
                    ));
                };
                let mut rew_bytes = Vec::new();
                row.args[sv.kprob_pos.of("rew")].encode(&mut rew_bytes);
                if !seen.insert((src_elem, act_elem, dst_elem, rew_bytes)) {
                    return Err(ctx_err(
                        name,
                        "two outcome rows share one (src, act, dst, rew) key — \
                         parallel outcomes (P-FUN territory), refusing"
                            .into(),
                    ));
                }
                let p = d.q_lit(&row.value, "kprob value")?;
                kernel
                    .entry((*s_idx, *a_idx))
                    .or_default()
                    .push((*d_idx, p));
            }
        }
    }
    // Reward-merge: same destination at different rewards sums.
    for grp in kernel.values_mut() {
        grp.sort_by_key(|(dst, _)| *dst);
        let mut merged: Vec<(usize, QQ)> = Vec::with_capacity(grp.len());
        for (dst, p) in grp.drain(..) {
            match merged.last_mut() {
                Some((last, acc)) if *last == dst => *acc = acc.add(&p),
                _ => merged.push((dst, p)),
            }
        }
        *grp = merged;
    }

    let mut init: Vec<(usize, QQ)> = Vec::new();
    {
        let dtmc_pos = sv.kinit_pos.of("dtmc");
        let state_pos = sv.kinit_pos.of("state");
        let mut seen: HashSet<u32> = HashSet::new();
        for row in rows.arg_rows(model) {
            if row.fun != sv.kinit {
                continue;
            }
            d.step()?;
            if d.elem(&row.args[dtmc_pos])? != model {
                continue;
            }
            let state_elem = d.elem(&row.args[state_pos])?;
            let Some(s_idx) = state_ids.get(&state_elem) else {
                return Err(ctx_err(
                    name,
                    "a kinit row cites a state outside the model's decoded state set \
                     — identity undecidable, refusing"
                        .into(),
                ));
            };
            if !seen.insert(state_elem) {
                return Err(ctx_err(
                    name,
                    "two kinit rows for one state — ambiguous (P-FUN territory), \
                     refusing"
                        .into(),
                ));
            }
            init.push((*s_idx, d.q_lit(&row.value, "kinit value")?));
        }
    }
    if init.is_empty() {
        return Err(ctx_err(
            name,
            "the model carries no kinit rows — the init distribution is not in \
             view, refusing"
                .into(),
        ));
    }

    let mut policy: HashMap<(usize, usize), usize> = HashMap::new();
    {
        let pol_pos = sv.pact_pos.of("pol");
        let psrc_pos = sv.pact_pos.of("src");
        let t_pos = sv.pact_pos.of("t");
        for row in rows.arg_rows(pol) {
            if row.fun != sv.pact {
                continue;
            }
            d.step()?;
            if d.elem(&row.args[pol_pos])? != pol {
                continue;
            }
            let src_elem = d.elem(&row.args[psrc_pos])?;
            let Some(s_idx) = state_ids.get(&src_elem) else {
                return Err(ctx_err(
                    name,
                    "a choice row cites a state outside the model's decoded state \
                     set — identity undecidable, refusing"
                        .into(),
                ));
            };
            if absorbing[*s_idx] {
                return Err(ctx_err(
                    name,
                    "a stored choice row at an absorbing source — nothing to choose \
                     (frame denial territory), refusing"
                        .into(),
                ));
            }
            let t = d.nat_lit(&row.args[t_pos], "pact/t")? as usize;
            let act_val = d.elem(&row.value)?;
            let Some(a_idx) = act_ids.get(&act_val) else {
                return Err(ctx_err(
                    name,
                    "a choice row picks an action outside the model's decoded \
                     alphabet — identity undecidable, refusing"
                        .into(),
                ));
            };
            if policy.insert((*s_idx, t), *a_idx).is_some() {
                return Err(ctx_err(
                    name,
                    "two choice rows at one (state, step) — parallel choices \
                     (P-FUN territory), refusing"
                        .into(),
                ));
            }
        }
    }

    Ok(DecodedModel {
        ns,
        absorbing,
        init,
        kernel,
        policy,
    })
}

/// The chain species: QSat/sys is a mechanism leaf whose chain content
/// rides the relational `mech_dtmc {mech, chain}` bridge; the one-step
/// law is the `dprob` rows (parallel edges unrepresentable — one row
/// per ordered state pair), the initial distribution the `dinit` rows.
/// The walk consumes it through the synthetic one-action view: every
/// group keyed at action 0, a total (state, step) → 0 policy, no
/// absorbing marks (an absorbing state is its stored self-loop row —
/// the frame's own schema decision). A state with no outgoing rows
/// fails the step obligation downstream (`NoKernelGroup`): the walk
/// demands the whole law, not a substochastic fragment.
fn decode_chain_model(
    d: &mut Decoder,
    rows: &CertRows,
    v: &DeadlineVocab,
    cv: &ChainDtmc,
    sys_row: &crate::rowctx::CtorRow,
    deadline: usize,
) -> Result<DecodedModel, EvalError> {
    let name = d.name;
    if sys_row.fun == v.sys_wire {
        return Err(ctx_err(
            name,
            "QSat/sys is a composite — the chain walk takes a mechanism leaf \
             (composed subjects are the composition patterns' territory), refusing"
                .into(),
        ));
    }
    if sys_row.fun != v.sys_mech {
        return Err(ctx_err(
            name,
            "QSat/sys is constructed by a fun outside the expected SysMech/SysWire \
             pair — malformed rows"
                .into(),
        ));
    }
    let [mech_cell] = sys_row.args.as_slice() else {
        return Err(ctx_err(name, "SysMech row arity mismatch".into()));
    };
    let mech = d.elem(mech_cell)?;

    // The chain via the relational bridge: the citation reading (the
    // record's bytewise wire order keys the subject index on `chain`,
    // so subject-scoped sweeps over the mech would miss the row).
    let chain_pos = cv.mech_dtmc_pos.of("chain");
    let mech_pos = cv.mech_dtmc_pos.of("mech");
    let mut model: Option<u32> = None;
    for r in rows.rel_rows_citing(mech) {
        if r.rel != cv.mech_dtmc {
            continue;
        }
        d.step()?;
        if r.args.len() != 2 {
            return Err(ctx_err(name, "mech_dtmc row arity mismatch".into()));
        }
        if d.elem(&r.args[mech_pos])? != mech {
            continue; // cites this element in another position
        }
        let k = d.elem(&r.args[chain_pos])?;
        match model {
            Some(prev) if prev != k => {
                return Err(ctx_err(
                    name,
                    "two chain-content rows on one mechanism — at most one chain per \
                     mechanism is admission conformance, refusing"
                        .into(),
                ));
            }
            _ => model = Some(k),
        }
    }
    let Some(model) = model else {
        return Err(ctx_err(
            name,
            "the mechanism carries no chain content in view — structure undecidable".into(),
        ));
    };

    // --- the chain's states: dense idx bijection ------------------------------
    let mut state_ids: HashMap<u32, usize> = HashMap::new();
    {
        let mut state_elems: Vec<u32> = Vec::new();
        for row in rows.producers(model) {
            if row.fun == cv.dstate_dtmc {
                let [subject] = row.args.as_slice() else {
                    return Err(ctx_err(name, "model-membership row arity mismatch".into()));
                };
                state_elems.push(d.elem(subject)?);
            }
        }
        if state_elems.len() > DEADLINE_MAX_STATES {
            return Err(ctx_err(
                name,
                "state alphabet beyond the budget — refusing".into(),
            ));
        }
        dense_ids(d, &state_elems, cv.dstate_idx, "DState/idx", &mut state_ids)?;
    }
    let ns = state_ids.len();
    if ns == 0 {
        return Err(ctx_err(
            name,
            "the chain has no states in view — structure undecidable".into(),
        ));
    }
    if (deadline + 1).saturating_mul(ns) > DEADLINE_MAX_CELLS {
        return Err(ctx_err(
            name,
            "(T+1)*ns beyond the cell budget — refusing".into(),
        ));
    }

    // --- outcome rows: at most one probability per ordered state pair --------
    let src_pos = cv.dprob_pos.of("src");
    let dst_pos = cv.dprob_pos.of("dst");
    let mut kernel: HashMap<(usize, usize), Vec<(usize, QQ)>> = HashMap::new();
    {
        let mut seen: HashSet<(u32, u32)> = HashSet::new();
        for (state_elem, s_idx) in &state_ids {
            for row in rows.arg_rows(*state_elem) {
                if row.fun != cv.dprob {
                    continue;
                }
                d.step()?;
                let src_elem = d.elem(&row.args[src_pos])?;
                if src_elem != *state_elem {
                    continue; // cited as dst here; the src's own sweep files it
                }
                let dst_elem = d.elem(&row.args[dst_pos])?;
                let Some(d_idx) = state_ids.get(&dst_elem) else {
                    return Err(ctx_err(
                        name,
                        "an outcome row cites a destination outside the chain's \
                         decoded state set — identity undecidable, refusing"
                            .into(),
                    ));
                };
                if !seen.insert((src_elem, dst_elem)) {
                    return Err(ctx_err(
                        name,
                        "two outcome rows share one (src, dst) pair — parallel edges \
                         (P-FUN territory), refusing"
                            .into(),
                    ));
                }
                let p = d.q_lit(&row.value, "dprob value")?;
                kernel
                    .entry((*s_idx, 0usize))
                    .or_default()
                    .push((*d_idx, p));
            }
        }
    }
    for grp in kernel.values_mut() {
        grp.sort_by_key(|(dst, _)| *dst);
    }

    // --- initial rows ----------------------------------------------------------
    let mut init: Vec<(usize, QQ)> = Vec::new();
    {
        let chain_fpos = cv.dinit_pos.of("chain");
        let state_fpos = cv.dinit_pos.of("state");
        let mut seen: HashSet<u32> = HashSet::new();
        for row in rows.arg_rows(model) {
            if row.fun != cv.dinit {
                continue;
            }
            d.step()?;
            if d.elem(&row.args[chain_fpos])? != model {
                continue;
            }
            let state_elem = d.elem(&row.args[state_fpos])?;
            let Some(s_idx) = state_ids.get(&state_elem) else {
                return Err(ctx_err(
                    name,
                    "a dinit row cites a state outside the chain's decoded state set \
                     — identity undecidable, refusing"
                        .into(),
                ));
            };
            if !seen.insert(state_elem) {
                return Err(ctx_err(
                    name,
                    "two dinit rows for one state — ambiguous (P-FUN territory), \
                     refusing"
                        .into(),
                ));
            }
            init.push((*s_idx, d.q_lit(&row.value, "dinit value")?));
        }
    }
    if init.is_empty() {
        return Err(ctx_err(
            name,
            "the chain carries no dinit rows — the init distribution is not in \
             view, refusing"
                .into(),
        ));
    }

    // --- the synthetic one-action view ------------------------------------------
    // No absorbing marks exist in this frame; the policy is total at
    // action 0 (its size is the already-budgeted (T+1)·ns cell scale).
    let absorbing = vec![false; ns];
    let mut policy: HashMap<(usize, usize), usize> = HashMap::with_capacity(ns * deadline);
    for t in 0..deadline {
        for s in 0..ns {
            policy.insert((s, t), 0);
        }
    }

    Ok(DecodedModel {
        ns,
        absorbing,
        init,
        kernel,
        policy,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::{BigInt, BigUint};

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    /// A hand-computed two-state cert: state 1 is the absorbing goal;
    /// from state 0, action 0 reaches it with probability 1/2 per
    /// step; T = 2. Exact hitting probability from 0: 3/4; the table
    /// is the exact backward induction.
    fn small() -> DeadlineCert {
        let mut kernel = HashMap::new();
        kernel.insert((0usize, 0usize), vec![(0usize, q(1, 2)), (1usize, q(1, 2))]);
        let mut policy = HashMap::new();
        policy.insert((0usize, 0usize), 0usize);
        policy.insert((0usize, 1usize), 0usize);
        DeadlineCert {
            face: Face::Ge,
            deadline: 2,
            ns: 2,
            goal: vec![false, true],
            absorbing: vec![false, true],
            init: vec![(0, q(1, 1))],
            claim: q(3, 4),
            kernel,
            policy,
            // t-major state-minor: V_0 = (3/4, 1), V_1 = (1/2, 1),
            // V_2 = (0, 1).
            table: vec![q(3, 4), q(1, 1), q(1, 2), q(1, 1), q(0, 1), q(1, 1)],
        }
    }

    #[test]
    fn small_cert_accepts() {
        assert_eq!(check_deadline(&small()), Ok(()));
    }

    #[test]
    fn claim_above_mixture_fails() {
        let mut c = small();
        c.claim = q(4, 5);
        assert_eq!(check_deadline(&c), Err(DeadlineViolation::Claim));
    }

    #[test]
    fn boundary_violation_fails() {
        let mut c = small();
        c.table[4] = q(1, 10); // V_2(0) > [0 in goal] = 0
        assert_eq!(
            check_deadline(&c),
            Err(DeadlineViolation::Boundary { s: 0 })
        );
    }

    #[test]
    fn step_violation_fails() {
        let mut c = small();
        c.table[0] = q(7, 8); // V_0(0) > 1/2*V_1(0) + 1/2*V_1(1) = 3/4
        c.claim = q(0, 1);
        assert_eq!(
            check_deadline(&c),
            Err(DeadlineViolation::Step { s: 0, t: 0 })
        );
    }

    #[test]
    fn group_sum_violation_fails() {
        let mut c = small();
        c.kernel.get_mut(&(0, 0)).unwrap()[0].1 = q(1, 3);
        assert_eq!(
            check_deadline(&c),
            Err(DeadlineViolation::KernelGroupSum { src: 0, act: 0 })
        );
    }

    #[test]
    fn prob_range_violation_fails() {
        let mut c = small();
        c.kernel.get_mut(&(0, 0)).unwrap()[0].1 = q(0, 1);
        assert_eq!(
            check_deadline(&c),
            Err(DeadlineViolation::KernelProbRange { src: 0, act: 0 })
        );
    }

    #[test]
    fn entry_range_violation_fails() {
        let mut c = small();
        c.table[1] = q(9, 8);
        assert_eq!(
            check_deadline(&c),
            Err(DeadlineViolation::EntryRange { t: 0, s: 1 })
        );
    }

    #[test]
    fn missing_policy_fails() {
        let mut c = small();
        c.policy.remove(&(0, 1));
        assert_eq!(
            check_deadline(&c),
            Err(DeadlineViolation::PolicyUnresolved { s: 0, t: 1 })
        );
    }

    #[test]
    fn table_shape_violation_fails() {
        let mut c = small();
        c.table.pop();
        assert_eq!(
            check_deadline(&c),
            Err(DeadlineViolation::TableShape { got: 5, want: 6 })
        );
    }

    #[test]
    fn init_mixture_is_the_c_obligation() {
        // Split the init mass: 1/2 on each state. Mixture of V_0 =
        // 1/2 * 3/4 + 1/2 * 1 = 7/8.
        let mut c = small();
        c.init = vec![(0, q(1, 2)), (1, q(1, 2))];
        c.claim = q(7, 8);
        assert_eq!(check_deadline(&c), Ok(()));
        c.claim = q(9, 10);
        assert_eq!(check_deadline(&c), Err(DeadlineViolation::Claim));
    }

    #[test]
    fn init_mass_obligations() {
        let mut c = small();
        c.init = vec![(0, q(1, 2))]; // sums to 1/2
        assert_eq!(check_deadline(&c), Err(DeadlineViolation::InitMass));
        let mut c = small();
        c.init = vec![(0, q(0, 1)), (1, q(1, 1))]; // zero mass stored
        assert_eq!(check_deadline(&c), Err(DeadlineViolation::InitMass));
    }

    #[test]
    fn absorbing_nongoal_self_loop_step() {
        // A third, absorbing NON-goal state (a hole): V must be
        // non-increasing along its determined self-loop.
        let mut kernel = HashMap::new();
        kernel.insert((0usize, 0usize), vec![(1usize, q(1, 2)), (2usize, q(1, 2))]);
        let mut policy = HashMap::new();
        policy.insert((0usize, 0usize), 0usize);
        let base = DeadlineCert {
            face: Face::Ge,
            deadline: 1,
            ns: 3,
            goal: vec![false, true, false],
            absorbing: vec![false, true, true],
            init: vec![(0, q(1, 1))],
            claim: q(1, 2),
            kernel,
            policy,
            // V_0 = (1/2, 1, 0), V_1 = (0, 1, 0).
            table: vec![q(1, 2), q(1, 1), q(0, 1), q(0, 1), q(1, 1), q(0, 1)],
        };
        assert_eq!(check_deadline(&base), Ok(()));
        // Hole value increasing across the self-loop step: violation.
        let mut c = base.clone();
        c.table[2] = q(1, 4); // V_0(2) = 1/4 > V_1(2) = 0
        c.claim = q(0, 1);
        // Note (C)'s range pass admits 1/4; the step arm catches it.
        assert_eq!(
            check_deadline(&c),
            Err(DeadlineViolation::Step { s: 2, t: 0 })
        );
    }

    // --- the LE face (super-solution direction) ---------------------------

    /// The exact `small()` table read as an UPPER-bound certificate:
    /// exactness satisfies both faces, so the same table accepts at
    /// claim = 3/4 (the exact value) under LE.
    fn small_le() -> DeadlineCert {
        let mut c = small();
        c.face = Face::Le;
        c.claim = q(3, 4);
        c
    }

    #[test]
    fn le_exact_table_accepts() {
        assert_eq!(check_deadline(&small_le()), Ok(()));
        // A looser upper bound accepts too.
        let mut c = small_le();
        c.claim = q(9, 10);
        assert_eq!(check_deadline(&c), Ok(()));
    }

    #[test]
    fn le_claim_below_mixture_fails() {
        // q below the true value: the mixture exceeds the claimed
        // upper bound.
        let mut c = small_le();
        c.claim = q(1, 2);
        assert_eq!(check_deadline(&c), Err(DeadlineViolation::ClaimLe));
    }

    #[test]
    fn le_boundary_below_indicator_fails() {
        // V_T at the goal lowered below 1: no longer a super-solution
        // at the deadline.
        let mut c = small_le();
        c.table[5] = q(1, 2); // V_2(goal) = 1/2 < 1
        assert_eq!(
            check_deadline(&c),
            Err(DeadlineViolation::BoundaryLe { s: 1 })
        );
    }

    #[test]
    fn le_goal_floor_is_explicit() {
        // The on-goal interior row lowered below 1 — the GE range
        // pass would admit it; the LE face's explicit floor refuses.
        let mut c = small_le();
        c.table[3] = q(1, 2); // V_1(goal) = 1/2 < 1
        assert_eq!(
            check_deadline(&c),
            Err(DeadlineViolation::GoalLe { s: 1, t: 1 })
        );
    }

    #[test]
    fn le_step_below_expectation_fails() {
        // V_0(0) lowered below the one-step expectation 3/4: an
        // under-approximation is no super-solution.
        let mut c = small_le();
        c.table[0] = q(1, 2);
        assert_eq!(
            check_deadline(&c),
            Err(DeadlineViolation::StepLe { s: 0, t: 0 })
        );
    }

    /// The exact_T5 shape in miniature: a goal unreachable within the
    /// horizon, table identically 0 off-goal, claim q = 0 — the
    /// possibilistic prohibition discharging on the exact table, no
    /// boundary special-case (q = 0 is interior to the LE face's
    /// canonical interval [0, 1)).
    #[test]
    fn le_zero_claim_prohibition() {
        // Two states, goal = 1, but the kernel LOOPS at 0 (never
        // reaches the goal): exact V_t(0) = 0 for all t.
        let mut kernel = HashMap::new();
        kernel.insert((0usize, 0usize), vec![(0usize, q(1, 1))]);
        let mut policy = HashMap::new();
        policy.insert((0usize, 0usize), 0usize);
        policy.insert((0usize, 1usize), 0usize);
        let base = DeadlineCert {
            face: Face::Le,
            deadline: 2,
            ns: 2,
            goal: vec![false, true],
            absorbing: vec![false, true],
            init: vec![(0, q(1, 1))],
            claim: q(0, 1),
            kernel,
            policy,
            // V_t = (0, 1) at every t.
            table: vec![q(0, 1), q(1, 1), q(0, 1), q(1, 1), q(0, 1), q(1, 1)],
        };
        assert_eq!(check_deadline(&base), Ok(()));
        // The designed T5 mutant shape: V_0(init) raised above 0 —
        // the super-solution survives (S is >=), and the claim
        // obligation is the single falsifier.
        let mut c = base.clone();
        c.table[0] = q(1, 2);
        assert_eq!(check_deadline(&c), Err(DeadlineViolation::ClaimLe));
        // The same perturbed table under the GE face at p = 0 would
        // fail STEP instead (the sub-solution direction breaks) —
        // the two faces falsify at different obligations, which is
        // the direction-of-inequality content made testable.
        let mut g = c.clone();
        g.face = Face::Ge;
        assert_eq!(
            check_deadline(&g),
            Err(DeadlineViolation::Step { s: 0, t: 0 })
        );
    }
}
