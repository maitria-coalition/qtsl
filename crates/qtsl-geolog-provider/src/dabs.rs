//! The DtmcAbsorb family: finite-horizon absorption brackets for
//! stored-row chains (`qtsl_dabs_wf`, `qtsl_dabs_absorb_bracket`,
//! `qtsl_dabs_posterior_bracket`).
//!
//! Semantic authority: the DtmcAbsorb species theory
//! (`theories/DtmcAbsorb.geolog` — its header comment states the
//! whole evaluation semantics) over the chain species' stored grain
//! (`theories/Dtmc.geolog`: `dprob {src, dst} → Q` outcome rows,
//! `dinit {chain, state} → Q` initial rows; an absorbing state is its
//! explicit unit self-loop row or no stored row at all). The query
//! binds its chain through an ANCHOR STATE (`DAbsQuery/anchor`): the
//! query's chain is its anchor's chain.
//!
//! Evaluation semantics, restated at the walk's grain: write
//! `m_0` = the chain's dinit measure and `m_{t+1} = m_t · K`, where
//! `K` is the stored dprob rows COMPLETED by self-loops at every
//! state with no stored outgoing row (rowless-is-absorbing). For a
//! query `q` with horizon `T`, class labeling `dclass` and rejection
//! labeling `dreject`:
//!
//! - `N_c(q)` = `m_T` restricted to class-`c` states, summed;
//! - `S(q)`  = the sum of `N_c` over all classes;
//! - `R(q)`  = `1 − S(q) − (m_T restricted to rejected states,
//!   summed)` — the residual: alive, rowless-held, and
//!   unclassified-absorbed mass.
//!
//! The three side-conditions this module decides, exact-rational end
//! to end (bracket comparisons by cross-multiplication — no division
//! anywhere):
//!
//! - **`qtsl_dabs_wf {q}`** — every classed or rejected state of the
//!   query is stored-absorbing: no stored outgoing row, or exactly
//!   the unit self-loop. A labeled state that leaked mass would break
//!   the monotonicity the bridge lemmas rest on — decided FALSE.
//! - **`qtsl_dabs_absorb_bracket {q, class, lo, hi}`** — holds iff
//!   `lo ≤ N_c` and `N_c + R_c ≤ hi`, both recomputed by the T-step
//!   evaluation above, where `R_c` is the REACHABILITY-SHARPENED
//!   per-class residual: the residual mass restricted to states from
//!   which some class-`c` state is reachable through the stored rows'
//!   positive-probability edges (backward walk from the class's
//!   states; a rowless or unit-self-loop unclassified state reaches
//!   nothing and contributes zero). `R_c ≤ R` always, so every
//!   certificate admitted under the uniform-residual reading stays
//!   admissible — claims may be looser than canonical, never tighter.
//!   Soundness direction, stated carefully: the co-reachable set is
//!   not forward-closed, but its COMPLEMENT is (no positive stored
//!   inflow into the set exists from outside it), so the mass on it
//!   never grows and later class gain is bounded by `R_c`. The walk
//!   rides the same evaluation budget as the forward evolution —
//!   their costs are SUMMED against one cap, charged up front from
//!   lengths — and exhaustion refuses the whole claim, never a
//!   fallback to the uniform residual, never a verdict.
//! - **`qtsl_dabs_posterior_bracket {q, class, lo, hi}`** — holds iff
//!   `lo ≤ N_c/(S+R)` and `(N_c+R)/(S+R) ≤ hi`; REFUSES at `S = 0`
//!   (no positive evidence witness — the normalized measure's
//!   denominator is not witnessed positive, and the eventual
//!   conditional measure may be undefined).
//!
//! The bracket walks recompute the lawfulness of every row they
//! consume — the semantics' conservation reading presupposes it:
//! stored probabilities in (0, 1] with each present source group
//! summing to exactly one (C-DTMC-ROWMASS at the rows in view), init
//! masses in (0, 1] summing to exactly one (C-DTMC-INITMASS
//! likewise). Decided violations are `Ok(false)`, exactly the
//! deadline walk's posture on the same grain.
//!
//! Verdict discipline (the CtxArg pattern, inherited from
//! [`crate::deadline`]): decided violations of the obligations the
//! walk itself states are `Ok(false)`; anything the row context
//! cannot decide — unconstructed elements, duplicated attribute or
//! outcome rows (P-FUN territory), labels citing states outside the
//! decoded alphabet, a state both classed and rejected (the theory's
//! own refuse tier), exhausted budgets, `S = 0` posteriors — REFUSES,
//! never guessing.

use crate::error::EvalError;
use crate::qq::QQ;
use crate::roster::{DabsKind, EntryRow, RelKind};
use crate::rowctx::CertRows;
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use std::collections::{HashMap, HashSet};

/// Budgets: refusal beyond, never divergence (the P-ACYCLIC posture,
/// sized to the deadline family's precedents — states as
/// `DEADLINE_MAX_STATES`, total work as `DEADLINE_MAX_CELLS`).
pub const DABS_MAX_STATES: usize = 1 << 16;
/// The T-step evaluation's work bound: `horizon × (stored rows + ns)`
/// must stay within this budget (each step walks every stored row
/// plus the completion diagonal once).
pub const DABS_MAX_WORK: usize = 1 << 22;

/// Field lists in wire (bytewise field-name) order.
const F_WF: &[(&str, &str)] = &[("q", "DAbsQuery")];
const F_BRACKET: &[(&str, &str)] = &[
    ("class", "Nat"),
    ("hi", "Q"),
    ("lo", "Q"),
    ("q", "DAbsQuery"),
];

/// The DtmcAbsorb family's rows of the claimed roster (concatenated
/// at registration — provider.rs). Registration order is part of the
/// seam surface: append at the end, never reorder.
pub(crate) const ENTRIES: &[EntryRow] = &[
    ("qtsl_dabs_wf", F_WF, RelKind::Dabs(DabsKind::Wf)),
    (
        "qtsl_dabs_absorb_bracket",
        F_BRACKET,
        RelKind::Dabs(DabsKind::Absorb),
    ),
    (
        "qtsl_dabs_posterior_bracket",
        F_BRACKET,
        RelKind::Dabs(DabsKind::Posterior),
    ),
];

// ---------------------------------------------------------------------
// Vocabulary
// ---------------------------------------------------------------------

/// Field positions of a record-domain fun, resolved BY NAME at
/// vocabulary build (never assumed positional) — the deadline
/// family's pattern at this family's size.
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

/// The DtmcAbsorb vocabulary, pinned at vocabulary resolution (names
/// select, shapes verify, identities pin). Spans the chain species'
/// stored grain (`dprob`/`dinit`/`DState/dtmc`) plus the query
/// species' own declarations.
#[derive(Debug, Clone)]
pub struct DabsVocab {
    query_anchor: Chid,
    query_horizon: Chid,
    dstate_dtmc: Chid,
    dprob: Chid,
    dprob_pos: FieldPos,
    dinit: Chid,
    dinit_pos: FieldPos,
    dclass: Chid,
    dclass_pos: FieldPos,
    dreject: Chid,
    dreject_pos: FieldPos,
}

/// Build the DtmcAbsorb vocabulary for the named `DAbsQuery` sort.
/// `Err` → the family is not claimed (C-ORACLE safe-fail; reason
/// recorded on the provider's vocabulary notes).
pub fn build_dabs_vocab(indices: &[&TheoryIndex], query_sort: Chid) -> Result<DabsVocab, String> {
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
    // A record-domain declaration: field positions resolved by NAME
    // with per-field sort checks — robust to the declaration's wire
    // order. `relational` selects Prop-valued vs fun.
    let record_decl = |name: &str,
                       relational: bool,
                       want: &[(&str, &dyn Fn(&SortKey) -> bool)],
                       want_cod: Option<SortKey>|
     -> Result<(Chid, FieldPos), String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational != relational {
                return Err(format!(
                    "`{name}`: expected a {} declaration",
                    if relational { "relational" } else { "fun" }
                ));
            }
            if d.codomain != want_cod {
                return Err(format!("`{name}` has an unexpected codomain"));
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
        Err(format!("no `{name}` declaration among the swept revisions"))
    };

    let (query_anchor, qa_cod) = attr("DAbsQuery/anchor", query_sort)?;
    let SortKey::Elem(dstate_sort) = qa_cod else {
        return Err("`DAbsQuery/anchor` does not land in an element sort".into());
    };
    let (query_horizon, qh_cod) = attr("DAbsQuery/horizon", query_sort)?;
    if qh_cod != SortKey::Ground(Ground::Nat) {
        return Err("`DAbsQuery/horizon` does not land in Nat".into());
    }
    let (dstate_dtmc, dd_cod) = attr("DState/dtmc", dstate_sort)?;
    if !matches!(dd_cod, SortKey::Elem(_)) {
        return Err("`DState/dtmc` does not land in an element sort".into());
    }
    let is_state = |s: &SortKey| *s == SortKey::Elem(dstate_sort);
    let is_query = |s: &SortKey| *s == SortKey::Elem(query_sort);
    let is_elem = |s: &SortKey| matches!(s, SortKey::Elem(_));
    let (dprob, dprob_pos) = record_decl(
        "dprob",
        false,
        &[("src", &is_state), ("dst", &is_state)],
        Some(SortKey::Ground(Ground::Q)),
    )?;
    let (dinit, dinit_pos) = record_decl(
        "dinit",
        false,
        &[("chain", &is_elem), ("state", &is_state)],
        Some(SortKey::Ground(Ground::Q)),
    )?;
    let (dclass, dclass_pos) = record_decl(
        "dclass",
        false,
        &[("q", &is_query), ("state", &is_state)],
        Some(SortKey::Ground(Ground::Nat)),
    )?;
    let (dreject, dreject_pos) = record_decl(
        "dreject",
        true,
        &[("q", &is_query), ("state", &is_state)],
        None,
    )?;
    Ok(DabsVocab {
        query_anchor,
        query_horizon,
        dstate_dtmc,
        dprob,
        dprob_pos,
        dinit,
        dinit_pos,
        dclass,
        dclass_pos,
        dreject,
        dreject_pos,
    })
}

// ---------------------------------------------------------------------
// The pure obligation core (exposed so tests hit it directly)
// ---------------------------------------------------------------------

/// A decoded absorption query at the walk's grain, over a dense local
/// state indexing `0..ns` (the walk's own, minted from the decoded
/// alphabet — the chain species carries no table, so no stored
/// indexing is consulted).
#[derive(Debug, Clone)]
pub struct DabsQuery {
    pub ns: usize,
    pub horizon: usize,
    /// `(src, dst) → p`, stored rows only (the completion diagonal is
    /// structure, applied during the walk).
    pub rows: Vec<(usize, usize, QQ)>,
    /// `state → mass`, the chain's dinit rows.
    pub init: Vec<(usize, QQ)>,
    /// `state → class`, the query's class labeling.
    pub classed: HashMap<usize, u64>,
    /// The query's rejection labeling.
    pub rejected: Vec<usize>,
}

/// A decided violation — the named reason behind an `Ok(false)`
/// verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DabsViolation {
    /// A stored probability outside (0, 1].
    ProbRange { src: usize },
    /// A present source group's probabilities do not sum to 1.
    RowMass { src: usize },
    /// A dinit mass outside (0, 1], or masses not summing to 1.
    InitMass,
    /// (WF) a classed or rejected state with a stored outgoing row
    /// set other than the unit self-loop.
    LabeledLeak { s: usize },
    /// A bracket bound violated (`lo ≤ N_c` / `N_c + R ≤ hi`, or the
    /// posterior pair) — the claim does not hold.
    Bracket,
}

impl std::fmt::Display for DabsViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DabsViolation::ProbRange { src } => {
                write!(f, "stored probability at source {src} outside (0, 1]")
            }
            DabsViolation::RowMass { src } => {
                write!(f, "source {src}: stored masses do not sum to 1")
            }
            DabsViolation::InitMass => {
                write!(f, "dinit masses outside (0, 1] or not summing to 1")
            }
            DabsViolation::LabeledLeak { s } => {
                write!(f, "labeled state {s} is not stored-absorbing")
            }
            DabsViolation::Bracket => write!(f, "bracket bound violated"),
        }
    }
}

/// Row lawfulness shared by every walk that steps the kernel:
/// probabilities in (0, 1], each present source group summing to
/// exactly one, init masses a distribution.
fn check_rows(q: &DabsQuery) -> Result<(), DabsViolation> {
    use std::cmp::Ordering::*;
    let zero = QQ::zero();
    let one = QQ::one();
    let mut group: HashMap<usize, QQ> = HashMap::new();
    for (src, _dst, p) in &q.rows {
        if p.cmp_qq(&zero) != Greater || p.cmp_qq(&one) == Greater {
            return Err(DabsViolation::ProbRange { src: *src });
        }
        let acc = group.entry(*src).or_insert_with(QQ::zero);
        *acc = acc.add(p);
    }
    for (src, tot) in &group {
        if tot.cmp_qq(&one) != Equal {
            return Err(DabsViolation::RowMass { src: *src });
        }
    }
    let mut init_tot = QQ::zero();
    for (_s, m) in &q.init {
        if m.cmp_qq(&zero) != Greater || m.cmp_qq(&one) == Greater {
            return Err(DabsViolation::InitMass);
        }
        init_tot = init_tot.add(m);
    }
    if init_tot.cmp_qq(&one) != Equal {
        return Err(DabsViolation::InitMass);
    }
    Ok(())
}

/// (WF) every classed or rejected state is stored-absorbing: no
/// stored outgoing row, or exactly the unit self-loop.
pub fn check_dabs_wf(q: &DabsQuery) -> Result<(), DabsViolation> {
    use std::cmp::Ordering::*;
    let one = QQ::one();
    let labeled: HashSet<usize> = q
        .classed
        .keys()
        .copied()
        .chain(q.rejected.iter().copied())
        .collect();
    for s in labeled {
        let out: Vec<&(usize, usize, QQ)> = q.rows.iter().filter(|(src, _, _)| *src == s).collect();
        let absorbing = match out.as_slice() {
            [] => true,
            [(src, dst, p)] => src == dst && p.cmp_qq(&one) == Equal,
            _ => false,
        };
        if !absorbing {
            return Err(DabsViolation::LabeledLeak { s });
        }
    }
    Ok(())
}

/// The T-step measure evolution: `m_0` = dinit, `m_{t+1} = m_t · K`
/// with rowless sources completed by self-loops. Returns the horizon
/// measure — exact ℚ throughout. Row lawfulness is the caller's
/// (`check_rows`).
fn evolve_measure(q: &DabsQuery) -> Vec<QQ> {
    let has_rows: Vec<bool> = {
        let mut v = vec![false; q.ns];
        for (src, _, _) in &q.rows {
            v[*src] = true;
        }
        v
    };
    let mut m = vec![QQ::zero(); q.ns];
    for (s, mass) in &q.init {
        m[*s] = m[*s].add(mass);
    }
    for _t in 0..q.horizon {
        let mut next = vec![QQ::zero(); q.ns];
        for (src, dst, p) in &q.rows {
            if m[*src].is_zero() {
                continue;
            }
            next[*dst] = next[*dst].add(&m[*src].mul(p));
        }
        for s in 0..q.ns {
            if !has_rows[s] && !m[s].is_zero() {
                next[s] = next[s].add(&m[s]);
            }
        }
        m = next;
    }
    m
}

/// Aggregate the horizon measure into `(N_c, S, R)` for the claimed
/// class `c`.
fn aggregate(q: &DabsQuery, class: u64, m: &[QQ]) -> (QQ, QQ, QQ) {
    let mut n_c = QQ::zero();
    let mut s_all = QQ::zero();
    let mut rej = QQ::zero();
    for (state, c) in &q.classed {
        s_all = s_all.add(&m[*state]);
        if *c == class {
            n_c = n_c.add(&m[*state]);
        }
    }
    for state in &q.rejected {
        rej = rej.add(&m[*state]);
    }
    let r = QQ::one().sub(&s_all).sub(&rej);
    (n_c, s_all, r)
}

/// Compatibility wrapper: `(N_c, S, R)` with the UNIFORM residual —
/// the posterior form's reading (its one shared budget across
/// numerator and denominator is what makes the single normalizer
/// sound, so it deliberately does NOT take the sharpened residual).
fn evolve(q: &DabsQuery, class: u64) -> (QQ, QQ, QQ) {
    let m = evolve_measure(q);
    aggregate(q, class, &m)
}

/// The reachability-sharpened per-class residual `R_c`: the horizon
/// residual mass restricted to states from which some class-`c`
/// state is reachable through the stored rows' POSITIVE-probability
/// edges (filtered here explicitly — the walk never assumes the
/// range report ran). Backward walk, class states as seeds; a
/// rowless state has no edges and a unit-self-loop unclassified
/// state only its own, so neither reaches the class — each
/// contributes zero exactly as the species theory states. The
/// SHARED-budget charge (forward + walk, summed) lives at the
/// bracket's entry; the walk-local cap here is defense in depth for
/// direct callers — exhaustion refuses the WHOLE claim either way,
/// never a fallback to the uniform residual, never a verdict.
fn class_reach_residual(q: &DabsQuery, class: u64, m: &[QQ]) -> Result<QQ, String> {
    use std::cmp::Ordering::*;
    if q.ns.saturating_add(q.rows.len()) > DABS_MAX_WORK {
        return Err(
            "states + stored rows beyond the work budget for the class-reachability \
             walk — refusing the claim (never falling back to the uniform residual)"
                .into(),
        );
    }
    let zero = QQ::zero();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); q.ns];
    for (src, dst, p) in &q.rows {
        if p.cmp_qq(&zero) == Greater {
            preds[*dst].push(*src);
        }
    }
    let mut in_reach = vec![false; q.ns];
    let mut stack: Vec<usize> = Vec::new();
    for (state, c) in &q.classed {
        if *c == class && !in_reach[*state] {
            in_reach[*state] = true;
            stack.push(*state);
        }
    }
    while let Some(y) = stack.pop() {
        for &x in &preds[y] {
            if !in_reach[x] {
                in_reach[x] = true;
                stack.push(x);
            }
        }
    }
    // Residual support: unclassified, unrejected — the classed and
    // rejected buckets are already accounted outside R.
    let rejected: HashSet<usize> = q.rejected.iter().copied().collect();
    let mut r_c = QQ::zero();
    for (x, reach) in in_reach.iter().enumerate() {
        if *reach && !q.classed.contains_key(&x) && !rejected.contains(&x) && !m[x].is_zero() {
            r_c = r_c.add(&m[x]);
        }
    }
    Ok(r_c)
}

/// The unnormalized bracket: `lo ≤ N_c ∧ N_c + R_c ≤ hi`, with `R_c`
/// the reachability-sharpened per-class residual. Three-valued like
/// the posterior form: `Err` = refusal (the budget), decided
/// violations inside.
///
/// ONE shared budget: the walk rides the SAME evaluation budget as
/// the forward evolution — their costs are SUMMED (saturating) and
/// charged up front from lengths alone, before any stage runs, so a
/// claim whose stages each fit individually but whose total exceeds
/// the cap refuses as a whole: no verdict, no uniform-residual
/// fallback, no work done past the charge.
pub fn check_dabs_absorb(
    q: &DabsQuery,
    class: u64,
    lo: &QQ,
    hi: &QQ,
) -> Result<Result<(), DabsViolation>, String> {
    use std::cmp::Ordering::*;
    let per_pass = q.rows.len().saturating_add(q.ns);
    let forward = q.horizon.saturating_mul(per_pass);
    if forward.saturating_add(per_pass) > DABS_MAX_WORK {
        return Err(
            "forward evolution + reachability walk beyond the shared work budget — \
             refusing the whole claim (never falling back to the uniform residual)"
                .into(),
        );
    }
    if let Err(v) = check_rows(q) {
        return Ok(Err(v));
    }
    let m = evolve_measure(q);
    let (n_c, _s, _r) = aggregate(q, class, &m);
    let r_c = class_reach_residual(q, class, &m)?;
    if lo.cmp_qq(&n_c) == Greater || n_c.add(&r_c).cmp_qq(hi) == Greater {
        return Ok(Err(DabsViolation::Bracket));
    }
    Ok(Ok(()))
}

/// The normalized (posterior) bracket: `lo ≤ N_c/(S+R) ∧
/// (N_c+R)/(S+R) ≤ hi`, decided by cross-multiplication (`S + R > 0`
/// whenever `S > 0`, since `R ≥ 0` under conservation). `Ok(None)` =
/// holds; `Err` = decided violation; the `S = 0` refusal is the
/// caller's (it is a refusal, not a verdict, so it does not live in
/// the violation enum).
pub fn check_dabs_posterior(
    q: &DabsQuery,
    class: u64,
    lo: &QQ,
    hi: &QQ,
) -> Result<Result<(), DabsViolation>, String> {
    use std::cmp::Ordering::*;
    if let Err(v) = check_rows(q) {
        return Ok(Err(v));
    }
    let (n_c, s_all, r) = evolve(q, class);
    if s_all.is_zero() {
        return Err(
            "posterior bracket with no classed mass at the horizon (S = 0) — no \
             positive evidence witness, refusing"
                .into(),
        );
    }
    let den = s_all.add(&r);
    // lo ≤ N_c/den  ⟺  lo·den ≤ N_c   (den > 0);
    // (N_c+R)/den ≤ hi  ⟺  N_c+R ≤ hi·den.
    if lo.mul(&den).cmp_qq(&n_c) == Greater || n_c.add(&r).cmp_qq(&hi.mul(&den)) == Greater {
        return Ok(Err(DabsViolation::Bracket));
    }
    Ok(Ok(()))
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
    rows: &'a CertRows,
}

impl<'a> Decoder<'a> {
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

    /// The sole attribute row `fun(subject) = v`; absence and
    /// duplication both refuse (P-FUN posture at the attribute grain).
    fn need_attr(&self, subject: u32, fun: Chid, what: &str) -> Result<&'a Value, EvalError> {
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
        found.ok_or_else(|| {
            ctx_err(
                self.name,
                format!("element {subject} has no `{what}` row — structure undecidable"),
            )
        })
    }
}

/// Decode one absorption query from the row context: anchor → chain,
/// the chain's state alphabet, stored outcome and init rows, and the
/// query's labelings — refusing on everything the context cannot
/// decide.
fn decode_query(d: &Decoder, v: &DabsVocab, query: u32) -> Result<DabsQuery, EvalError> {
    let name = d.name;
    let rows = d.rows;

    // --- anchor → chain ---------------------------------------------------
    let anchor_val = d
        .need_attr(query, v.query_anchor, "DAbsQuery/anchor")?
        .clone();
    let anchor = d.elem(&anchor_val)?;
    let horizon_val = d
        .need_attr(query, v.query_horizon, "DAbsQuery/horizon")?
        .clone();
    let horizon_n = d.nat_lit(&horizon_val, "DAbsQuery/horizon")?;
    let chain_val = d.need_attr(anchor, v.dstate_dtmc, "DState/dtmc")?.clone();
    let chain = d.elem(&chain_val)?;

    // --- the chain's state alphabet (DState/dtmc rows carry the chain
    // as their VALUE cell), dense local indexing minted here ---------------
    let mut state_elems: Vec<u32> = Vec::new();
    for row in rows.producers(chain) {
        if row.fun != v.dstate_dtmc {
            continue;
        }
        let [subject] = row.args.as_slice() else {
            return Err(ctx_err(name, "DState/dtmc row arity mismatch".into()));
        };
        state_elems.push(d.elem(subject)?);
    }
    state_elems.sort_unstable();
    state_elems.dedup();
    if state_elems.len() > DABS_MAX_STATES {
        return Err(ctx_err(
            name,
            "state alphabet beyond the budget — refusing".into(),
        ));
    }
    let ids: HashMap<u32, usize> = state_elems
        .iter()
        .enumerate()
        .map(|(i, e)| (*e, i))
        .collect();
    let ns = ids.len();
    if ns == 0 {
        return Err(ctx_err(
            name,
            "the chain has no states in view — structure undecidable".into(),
        ));
    }

    // --- stored outcome rows (per-state sweep; the (src, dst) key is
    // functional — a repeat is a parallel edge, P-FUN territory) -----------
    let src_pos = v.dprob_pos.of("src");
    let dst_pos = v.dprob_pos.of("dst");
    let mut out_rows: Vec<(usize, usize, QQ)> = Vec::new();
    let mut seen_pairs: HashSet<(u32, u32)> = HashSet::new();
    for (state_elem, s_idx) in &ids {
        for row in rows.arg_rows(*state_elem) {
            if row.fun != v.dprob {
                continue;
            }
            let src_elem = d.elem(&row.args[src_pos])?;
            if src_elem != *state_elem {
                continue; // cited as dst here; the src's own sweep files it
            }
            let dst_elem = d.elem(&row.args[dst_pos])?;
            let Some(d_idx) = ids.get(&dst_elem) else {
                return Err(ctx_err(
                    name,
                    "an outcome row cites a destination outside the chain's decoded \
                     state set — identity undecidable, refusing"
                        .into(),
                ));
            };
            if !seen_pairs.insert((src_elem, dst_elem)) {
                return Err(ctx_err(
                    name,
                    "two outcome rows share one (src, dst) pair — parallel edges \
                     (P-FUN territory), refusing"
                        .into(),
                ));
            }
            let p = d.q_lit(&row.value, "dprob value")?;
            out_rows.push((*s_idx, *d_idx, p));
        }
    }

    // --- init rows (chain-keyed; the (chain, state) key is functional) ----
    let init_chain_pos = v.dinit_pos.of("chain");
    let init_state_pos = v.dinit_pos.of("state");
    let mut init: Vec<(usize, QQ)> = Vec::new();
    let mut seen_init: HashSet<u32> = HashSet::new();
    for row in rows.arg_rows(chain) {
        if row.fun != v.dinit {
            continue;
        }
        if d.elem(&row.args[init_chain_pos])? != chain {
            continue; // cited as a state here (impossible sort-wise) — skip
        }
        let state_elem = d.elem(&row.args[init_state_pos])?;
        let Some(s_idx) = ids.get(&state_elem) else {
            return Err(ctx_err(
                name,
                "an init row cites a state outside the chain's decoded state set — \
                 identity undecidable, refusing"
                    .into(),
            ));
        };
        if !seen_init.insert(state_elem) {
            return Err(ctx_err(
                name,
                "two init rows share one (chain, state) key — ambiguous (P-FUN \
                 territory), refusing"
                    .into(),
            ));
        }
        init.push((*s_idx, d.q_lit(&row.value, "dinit value")?));
    }

    // --- the query's labelings --------------------------------------------
    let class_q_pos = v.dclass_pos.of("q");
    let class_state_pos = v.dclass_pos.of("state");
    let mut classed: HashMap<usize, u64> = HashMap::new();
    let mut seen_class: HashSet<u32> = HashSet::new();
    for row in rows.arg_rows(query) {
        if row.fun != v.dclass {
            continue;
        }
        if d.elem(&row.args[class_q_pos])? != query {
            continue;
        }
        let state_elem = d.elem(&row.args[class_state_pos])?;
        let Some(s_idx) = ids.get(&state_elem) else {
            return Err(ctx_err(
                name,
                "a class label cites a state outside the query chain's decoded state \
                 set — identity undecidable, refusing"
                    .into(),
            ));
        };
        if !seen_class.insert(state_elem) {
            return Err(ctx_err(
                name,
                "a state classed twice for one query — ambiguous (P-FUN territory), \
                 refusing"
                    .into(),
            ));
        }
        let c = d.nat_lit(&row.value, "dclass value")?;
        classed.insert(*s_idx, c);
    }
    let rej_q_pos = v.dreject_pos.of("q");
    let rej_state_pos = v.dreject_pos.of("state");
    let mut rejected: Vec<usize> = Vec::new();
    let mut seen_rej: HashSet<u32> = HashSet::new();
    for row in rows.rel_rows_citing(query) {
        if row.rel != v.dreject {
            continue;
        }
        let Some(q_cell) = row.args.get(rej_q_pos) else {
            return Err(ctx_err(name, "dreject row arity mismatch".into()));
        };
        if d.elem(q_cell)? != query {
            continue;
        }
        let Some(state_cell) = row.args.get(rej_state_pos) else {
            return Err(ctx_err(name, "dreject row arity mismatch".into()));
        };
        let state_elem = d.elem(state_cell)?;
        let Some(s_idx) = ids.get(&state_elem) else {
            return Err(ctx_err(
                name,
                "a rejection label cites a state outside the query chain's decoded \
                 state set — identity undecidable, refusing"
                    .into(),
            ));
        };
        if !seen_rej.insert(state_elem) {
            continue; // set semantics: byte-identical relation rows are one row
        }
        if classed.contains_key(s_idx) {
            return Err(ctx_err(
                name,
                "a state both classed and rejected for one query — the theory's own \
                 refuse tier (labeling ambiguous), refusing"
                    .into(),
            ));
        }
        rejected.push(*s_idx);
    }

    // --- budgets ------------------------------------------------------------
    let horizon = usize::try_from(horizon_n)
        .map_err(|_| ctx_err(name, "horizon beyond the work budget — refusing".into()))?;
    let per_step = out_rows.len().saturating_add(ns);
    if horizon.saturating_mul(per_step) > DABS_MAX_WORK {
        return Err(ctx_err(
            name,
            "horizon × (stored rows + ns) beyond the work budget — refusing".into(),
        ));
    }

    Ok(DabsQuery {
        ns,
        horizon,
        rows: out_rows,
        init,
        classed,
        rejected,
    })
}

/// The DtmcAbsorb family's evaluation. Args in wire field order —
/// `wf`: `(q)`; brackets: `(class, hi, lo, q)`.
pub(crate) fn eval_dabs(
    name: &str,
    v: &DabsVocab,
    kind: DabsKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let d = Decoder { name, rows };
    match kind {
        DabsKind::Wf => {
            let query = d.elem(args[0])?;
            let q = decode_query(&d, v, query)?;
            Ok(check_dabs_wf(&q).is_ok())
        }
        DabsKind::Absorb => {
            let class = d.nat_lit(args[0], "class")?;
            let hi = d.q_lit(args[1], "hi")?;
            let lo = d.q_lit(args[2], "lo")?;
            let query = d.elem(args[3])?;
            let q = decode_query(&d, v, query)?;
            match check_dabs_absorb(&q, class, &lo, &hi) {
                Ok(verdict) => Ok(verdict.is_ok()),
                Err(refuse) => Err(ctx_err(name, refuse)),
            }
        }
        DabsKind::Posterior => {
            let class = d.nat_lit(args[0], "class")?;
            let hi = d.q_lit(args[1], "hi")?;
            let lo = d.q_lit(args[2], "lo")?;
            let query = d.elem(args[3])?;
            let q = decode_query(&d, v, query)?;
            match check_dabs_posterior(&q, class, &lo, &hi) {
                Ok(verdict) => Ok(verdict.is_ok()),
                Err(refuse) => Err(ctx_err(name, refuse)),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::{BigInt, BigUint};

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    /// The die-paradox chain at the pure core's grain: states
    /// 0 = alive, 1 = acc (classed 0), 2 = rej (rejected); rows
    /// alive → acc 1/6, alive → alive 1/3, alive → rej 1/2; the
    /// labeled states rowless (the completion diagonal holds them).
    fn die(horizon: usize) -> DabsQuery {
        DabsQuery {
            ns: 3,
            horizon,
            rows: vec![(0, 1, q(1, 6)), (0, 0, q(1, 3)), (0, 2, q(1, 2))],
            init: vec![(0, q(1, 1))],
            classed: [(1usize, 0u64)].into_iter().collect(),
            rejected: vec![2],
        }
    }

    /// Canonical values at T = 10: `N_0 = 14762/59049` (the partial
    /// geometric sum `(1/6)·(1−(1/3)^10)/(1−1/3)`), `R = (1/3)^10 =
    /// 1/59049` — and the alive state reaches the class, so the
    /// sharpened `R_0` EQUALS the uniform residual here and
    /// `N_0 + R_0 = 4921/19683`. The tight bracket accepts with
    /// equality on both ends; strictly tighter on either end rejects —
    /// pinning both recomputed values exactly.
    #[test]
    fn die_paradox_exact_bracket() {
        let dq = die(10);
        let n0 = q(14762, 59049);
        let n0r = q(4921, 19683);
        assert!(check_dabs_absorb(&dq, 0, &n0, &n0r).unwrap().is_ok());
        // Strictly tighter low end: lo just above N_0.
        let lo_tight = q(14763, 59050);
        assert!(lo_tight.cmp_qq(&n0) == std::cmp::Ordering::Greater);
        assert_eq!(
            check_dabs_absorb(&dq, 0, &lo_tight, &n0r).unwrap(),
            Err(DabsViolation::Bracket)
        );
        // Strictly tighter high end: hi just below N_0 + R_0.
        assert_eq!(
            check_dabs_absorb(&dq, 0, &n0, &q(14762, 59049)).unwrap(),
            Err(DabsViolation::Bracket)
        );
        // A claim on a class no state carries: N_1 = 0 and — under
        // the sharpened residual — R_1 = 0 (no seeds, nothing
        // co-reachable): the canonical width is ZERO. The exact
        // point bracket accepts (under the uniform residual this hi
        // would have been rejected — the acceptance is the
        // sharpening's own liveness witness: revert the sharpening
        // and this line fails)…
        assert!(check_dabs_absorb(&dq, 1, &q(0, 1), &q(0, 1))
            .unwrap()
            .is_ok());
        // … looser claims stay admissible (the old uniform-width
        // shapes included) …
        assert!(check_dabs_absorb(&dq, 1, &q(0, 1), &q(1, 59049))
            .unwrap()
            .is_ok());
        assert!(check_dabs_absorb(&dq, 1, &q(0, 1), &q(1, 59050))
            .unwrap()
            .is_ok());
        // … and the low end still bites: lo > N_1 = 0 rejects.
        assert_eq!(
            check_dabs_absorb(&dq, 1, &q(1, 59049), &q(1, 1)).unwrap(),
            Err(DabsViolation::Bracket)
        );
    }

    /// The beauquier shape (the brief's named regression): a chain
    /// whose claimed class is UNREACHABLE from every alive state —
    /// the class label sits on an orphan absorbing state no positive
    /// row feeds. Canonical width for that class is 0 at any T ≥ 1,
    /// and the OLD uniform-width claim still ACCEPTs
    /// (claims-may-be-looser, exercised).
    #[test]
    fn unreachable_class_width_zero() {
        // 0 = alive, 1 = acc (classed 0), 2 = orphan (classed 1,
        // rowless, no inbound rows). Rows: alive → acc 1/2,
        // alive → alive 1/2.
        let dq = DabsQuery {
            ns: 3,
            horizon: 5,
            rows: vec![(0, 1, q(1, 2)), (0, 0, q(1, 2))],
            init: vec![(0, q(1, 1))],
            classed: [(1usize, 0u64), (2usize, 1u64)].into_iter().collect(),
            rejected: vec![],
        };
        // Class 1: N_1 = 0, R_1 = 0 — the point bracket [0, 0]
        // accepts. Under the uniform residual (R = (1/2)^5 = 1/32)
        // this hi would have rejected: this line is the sharpening's
        // mutant-direction witness.
        assert!(check_dabs_absorb(&dq, 1, &q(0, 1), &q(0, 1))
            .unwrap()
            .is_ok());
        // The old uniform-width claim [0, 1/32] still accepts.
        assert!(check_dabs_absorb(&dq, 1, &q(0, 1), &q(1, 32))
            .unwrap()
            .is_ok());
        // Class 0 keeps the full residual: alive reaches acc, so
        // R_0 = 1/32 and hi below N_0 + R_0 rejects.
        let n0 = q(31, 32);
        assert!(check_dabs_absorb(&dq, 0, &n0, &q(1, 1)).unwrap().is_ok());
        assert_eq!(
            check_dabs_absorb(&dq, 0, &n0, &n0).unwrap(),
            Err(DabsViolation::Bracket)
        );
    }

    /// Whole-budget refusal at the walk-heavy extreme: horizon zero
    /// (no evolution steps) with a state count past the cap refuses
    /// the whole claim up front — never a fallback to the uniform
    /// residual, never a verdict. (This shape sits past
    /// DABS_MAX_STATES too, so it is pure-core-only; the
    /// production-reachable boundary is the split-budget test below.)
    #[test]
    fn reach_walk_budget_refuses_whole_claim() {
        let ns = DABS_MAX_WORK + 2;
        let dq = DabsQuery {
            ns,
            horizon: 0,
            rows: vec![(0, 1, q(1, 1))],
            init: vec![(0, q(1, 1))],
            classed: [(1usize, 0u64)].into_iter().collect(),
            rejected: vec![],
        };
        let err =
            check_dabs_absorb(&dq, 0, &q(0, 1), &q(1, 1)).expect_err("the shared budget refuses");
        assert!(err.contains("budget"), "{err}");
        assert!(err.contains("uniform residual"), "{err}");
        // Same shape, small alphabet: verdicts normally.
        let small = DabsQuery { ns: 3, ..dq };
        assert!(check_dabs_absorb(&small, 0, &q(0, 1), &q(1, 1))
            .unwrap()
            .is_ok());
        // The walk-local cap (defense in depth for direct callers)
        // refuses on its own too; it fires before any indexing, so
        // the deliberately short measure vector is never touched.
        let big = DabsQuery {
            ns: DABS_MAX_WORK + 2,
            horizon: 0,
            rows: vec![],
            init: vec![(0, q(1, 1))],
            classed: [(1usize, 0u64)].into_iter().collect(),
            rejected: vec![],
        };
        let m = vec![QQ::zero(); 2];
        assert!(class_reach_residual(&big, 0, &m).is_err());
    }

    /// The SPLIT-BUDGET boundary, production-reachable: each stage
    /// individually under the cap — the forward evolution's charge
    /// and the walk's charge each fit, and the shape passes the
    /// decoder's own gates (`ns` far below DABS_MAX_STATES; the
    /// stored rows one lawful source group) — but their SUM exceeds
    /// the one budget the species contract names, so the whole claim
    /// REFUSES. (Before the shared-budget repair, both independent
    /// checks passed and the claim verdicted.)
    #[test]
    fn split_budget_sum_refuses_whole_claim() {
        // n identical rows alive → acc at 1/n each: one lawful group
        // (mass exactly one) the production decoder could carry.
        let n = DABS_MAX_WORK / 2 + 1024;
        let p = QQ::new(BigInt::from(1), BigUint::from(n));
        let dq = DabsQuery {
            ns: 3,
            horizon: 1,
            rows: vec![(0usize, 1usize, p); n],
            init: vec![(0, q(1, 1))],
            classed: [(1usize, 0u64)].into_iter().collect(),
            rejected: vec![],
        };
        let per_pass = dq.rows.len() + dq.ns;
        let forward = dq.horizon * per_pass;
        assert!(forward <= DABS_MAX_WORK, "forward stage fits alone");
        assert!(per_pass <= DABS_MAX_WORK, "walk stage fits alone");
        assert!(forward + per_pass > DABS_MAX_WORK, "the sum crosses");
        let err = check_dabs_absorb(&dq, 0, &q(0, 1), &q(1, 1))
            .expect_err("the summed budget refuses the whole claim");
        assert!(err.contains("shared work budget"), "{err}");
        assert!(err.contains("uniform residual"), "{err}");
    }

    /// The walk filters on p > 0 itself (never assuming the range
    /// report ran): a zero-probability stored edge into the class
    /// creates no co-reachability. Driven at the walk's own grain —
    /// the lawfulness gate would refuse the row upstream in the
    /// bracket path, which is exactly why the filter needs its own
    /// witness.
    #[test]
    fn reach_walk_filters_zero_edges() {
        let dq = DabsQuery {
            ns: 3,
            horizon: 1,
            // alive → acc at probability ZERO (unlawful upstream;
            // the walk must not read it as an edge), alive → alive 1.
            rows: vec![(0, 1, q(0, 1)), (0, 0, q(1, 1))],
            init: vec![(0, q(1, 1))],
            classed: [(1usize, 0u64)].into_iter().collect(),
            rejected: vec![],
        };
        let m = evolve_measure(&dq);
        let r_c = class_reach_residual(&dq, 0, &m).expect("walk runs");
        assert!(r_c.is_zero(), "a zero edge must not carry reachability");
    }

    /// The posterior bracket at T = 10: `[N_0/(S+R), (N_0+R)/(S+R)]
    /// = [14762/14763, 1]` (one class, so the numerator of the upper
    /// endpoint IS the denominator). Tight accepts; tighter rejects;
    /// the order-violated claim (lo > hi) is unsatisfiable.
    #[test]
    fn die_paradox_posterior() {
        let dq = die(10);
        let lo = q(14762, 14763);
        let hi = q(1, 1);
        assert!(check_dabs_posterior(&dq, 0, &lo, &hi)
            .expect("S > 0")
            .is_ok());
        assert_eq!(
            check_dabs_posterior(&dq, 0, &q(14763, 14764), &hi).expect("S > 0"),
            Err(DabsViolation::Bracket)
        );
        assert_eq!(
            check_dabs_posterior(&dq, 0, &lo, &q(14762, 14763)).expect("S > 0"),
            Err(DabsViolation::Bracket)
        );
        // lo > hi: no N_c can satisfy both ends (R ≥ 0).
        assert_eq!(
            check_dabs_posterior(&dq, 0, &q(1, 1), &q(14762, 14763)).expect("S > 0"),
            Err(DabsViolation::Bracket)
        );
    }

    /// `S = 0` refuses (no positive evidence witness), and it is a
    /// refusal — never a verdict either way.
    #[test]
    fn posterior_zero_classed_mass_refuses() {
        let mut dq = die(10);
        // Class an orphan state nothing ever reaches; retire the
        // reachable class label.
        dq.ns = 4;
        dq.classed = [(3usize, 0u64)].into_iter().collect();
        let err = check_dabs_posterior(&dq, 0, &q(0, 1), &q(1, 1)).expect_err("S = 0 refuses");
        assert!(err.contains("S = 0"), "{err}");
    }

    /// (WF) rowless and unit-self-loop labeled states pass; a leaked
    /// row, a sub-unit self-loop, and a self-loop beside a second row
    /// each fail.
    #[test]
    fn wf_stored_absorbing_shapes() {
        // Rowless labeled states (the die chain): pass.
        assert!(check_dabs_wf(&die(10)).is_ok());
        // Unit self-loop stored at the classed state: pass.
        let mut dq = die(10);
        dq.rows.push((1, 1, q(1, 1)));
        assert!(check_dabs_wf(&dq).is_ok());
        // A leaking row at the classed state: fail.
        let mut dq = die(10);
        dq.rows.push((1, 0, q(1, 1)));
        assert_eq!(check_dabs_wf(&dq), Err(DabsViolation::LabeledLeak { s: 1 }));
        // A sub-unit self-loop: fail (mass leaks through the
        // completion's absence — the row set is not the unit loop).
        let mut dq = die(10);
        dq.rows.push((2, 2, q(9, 10)));
        assert_eq!(check_dabs_wf(&dq), Err(DabsViolation::LabeledLeak { s: 2 }));
        // Unit self-loop beside a second stored row: fail.
        let mut dq = die(10);
        dq.rows.push((1, 1, q(1, 1)));
        dq.rows.push((1, 0, q(1, 59049)));
        assert_eq!(check_dabs_wf(&dq), Err(DabsViolation::LabeledLeak { s: 1 }));
    }

    /// Row lawfulness is recomputed by the bracket walks: a present
    /// group summing under one, a probability at zero, and a lying
    /// init measure are each decided violations.
    #[test]
    fn bracket_recomputes_row_lawfulness() {
        let mut dq = die(10);
        dq.rows[2] = (0, 2, q(1, 3)); // group now sums to 5/6
        assert_eq!(
            check_dabs_absorb(&dq, 0, &q(0, 1), &q(1, 1)).unwrap(),
            Err(DabsViolation::RowMass { src: 0 })
        );
        let mut dq = die(10);
        dq.rows.push((1, 1, q(0, 1))); // zero entry stored
        assert_eq!(
            check_dabs_absorb(&dq, 0, &q(0, 1), &q(1, 1)).unwrap(),
            Err(DabsViolation::ProbRange { src: 1 })
        );
        let mut dq = die(10);
        dq.init = vec![(0, q(1, 2))]; // not a distribution
        assert_eq!(
            check_dabs_absorb(&dq, 0, &q(0, 1), &q(1, 1)).unwrap(),
            Err(DabsViolation::InitMass)
        );
    }

    /// Horizon zero is the identity evolution: `m_T = dinit`, so the
    /// classed mass is zero and everything unrejected is residual
    /// (and the alive state reaches the class, so the sharpened
    /// residual is the full one here).
    #[test]
    fn horizon_zero_is_dinit() {
        let dq = die(0);
        // N_0 = 0, R_0 = R = 1 (all mass alive, co-reachable).
        assert!(check_dabs_absorb(&dq, 0, &q(0, 1), &q(1, 1))
            .unwrap()
            .is_ok());
        assert_eq!(
            check_dabs_absorb(&dq, 0, &q(1, 59049), &q(1, 1)).unwrap(),
            Err(DabsViolation::Bracket)
        );
    }
}
