//! The DtmcContraction family: score-carrying regional contraction
//! certificates over stored-row chains — the R18 demand
//! (`qtsl_dtmc_genform_contraction`) and its four claim relations
//! (`qtsl_dgc_partial_lo`, `qtsl_dgc_ev_bracket`,
//! `qtsl_dgc_survival_tail`, `qtsl_dgc_z_one`).
//!
//! Semantic authority: the DtmcContraction species theory
//! (`theories/DtmcContraction.geolog`) over the chain species' stored
//! grain (`theories/Dtmc.geolog`: `dprob` outcome rows, `dinit`
//! initial rows). This module carries the FINITE face only — the
//! alive region is exactly the stored `dweight` support, every
//! quantity is recomputed from stored rows, and derived constants
//! (the exit-domination reciprocal) are never stored. The
//! pattern/product-profile face (finitely presented infinite chains)
//! is deliberately absent this event: it was descoped to its own
//! design leg at data-plane review, and its certificates stay on the
//! experiments repo's dev-oracle lane.
//!
//! Evaluation semantics, restated at the walk's grain. Write `A` for
//! the alive region (the `dweight` support), `V` for the stored
//! weights on `A`, and evolve the KILLED-ON-EXIT measure: `m_0` = the
//! chain's dinit measure restricted to `A`, and `m_{t+1}` = `m_t · K`
//! restricted to `A`, where `K` is the stored rows completed by
//! self-loops at rowless states (rowless-is-absorbing, the chain
//! species' law — a rowless region state therefore HOLDS its mass).
//! Mass leaving `A` never returns (no re-entry is a refusal-checked
//! premise), so with `T` = the first exit from `A`:
//!
//! - `surv[t]` = the total mass of `m_t` = `P[T > t]`, exactly;
//! - `L` = `Σ_{t ∈ [offset, horizon)} surv[t]` — the exact partial
//!   survival sum, prologue subtracted;
//! - `W` = `Σ_{x ∈ A} m_horizon(x) · V(x)` — the weighted alive mass
//!   at the horizon;
//! - `κ` = `1 / min_A V` — DERIVED, never stored; the conversion from
//!   weighted decay to bare region mass (`P[T > n] ≤ κ · W(n)` for
//!   any positive `V`; a non-positive minimum has no conversion and
//!   REFUSES the claims that spend one).
//!
//! The demand and the claims, each recomputed per evaluation
//! (claims may be looser than canonical, never tighter):
//!
//! - **`qtsl_dtmc_genform_contraction {cw}`** (R18) — per-region-state
//!   contraction under the completed kernel
//!   (`Σ_{y ∈ A} K(x,y)V(y) ≤ c·V(x)`, exits contributing zero),
//!   no re-entry, the shape/range demands, the positive region
//!   minimum, the offset prologue determinism where the witness
//!   declares one, and the cross-face same-chain check where
//!   absorption queries share the container.
//! - **`qtsl_dgc_partial_lo {cw, lo}`** — `lo ≤ L`.
//! - **`qtsl_dgc_ev_bracket {cw, lo, hi}`** — `lo ≤ L` and
//!   `hi ≥ L + κ·W/(1−c)`; demands `c < 1` (the geometric assembly)
//!   and a positive weight minimum (the conversion).
//! - **`qtsl_dgc_survival_tail {cw, coeff, rate}`** —
//!   `P[T > n] ≤ coeff · rate^n` for all `n ≥ horizon`, discharged as
//!   `rate ∈ [c, 1)`, `coeff ≥ 0`, and
//!   `coeff · rate^horizon ≥ κ·W`; demands `c < 1` and the positive
//!   minimum.
//! - **`qtsl_dgc_z_one {cw}`** — termination mass exactly one:
//!   stored row mass one at every region state, positive weight
//!   minimum, and geometric decay at `c < 1` — what warrants reading
//!   the survival-form bracket as the raw first moment (off-region
//!   initial mass has `T = 0` and terminates trivially).
//!
//! Anchor offset (`k`, absent = 0): the EV/moment claims bind
//! `E[T − k]` for a DETERMINISTIC prologue — the evaluator recomputes
//! `P[T > k−1] = 1` from the stored rows (all mass still inside the
//! region at step `k−1`) and refuses otherwise; `k = 0` is vacuously
//! deterministic, `k > horizon` refuses. The horizon is ABSOLUTE
//! time, never post-offset.
//!
//! Verdict discipline (the CtxArg pattern, inherited from
//! [`crate::dabs`]): decided violations of the obligations the walk
//! itself states are `Ok(false)` — a refuted transfer inequality, a
//! claim bound outside its recomputed value; anything the rows
//! cannot warrant either way REFUSES with a reason — unlawful stored
//! rows (the first-moment reading has no sound truncation, the
//! dev-oracle posture), re-entry, rates outside `[0, 1]`, a missing
//! conversion (non-positive weight minimum), an undischargeable
//! prologue, exhausted budgets, and a PRESENT score field (the
//! score face is deferred-safe-fail this event: the mechanized core
//! is score-carrying, the evaluator seam refuses rather than
//! guessing).

use crate::error::EvalError;
use crate::qq::QQ;
use crate::roster::{DgcKind, EntryRow, RelKind};
use crate::rowctx::CertRows;
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use std::collections::{HashMap, HashSet};

/// Budgets: refusal beyond, never divergence (the DtmcAbsorb family's
/// idiom at this family's grain).
pub const DGC_MAX_STATES: usize = 1 << 16;
/// The WHOLE evaluation's work bound, charged up front from lengths:
/// `(horizon + 1) × (stored rows + states)` must stay within budget —
/// the `+ 1` charges the one-time recomputes (lawfulness, region,
/// no-re-entry, the one-pass transfer, the readout) so the formula
/// floors correctly at horizon zero, and `states` (not merely the
/// region) is charged because each evolution step allocates and
/// totals the full dense vector. Each stage makes a bounded number
/// of passes; the constant is folded into the cap's sizing.
pub const DGC_MAX_WORK: usize = 1 << 22;

/// Field lists in wire (bytewise field-name) order.
const F_CW: &[(&str, &str)] = &[("cw", "DGenContraction")];
const F_PARTIAL: &[(&str, &str)] = &[("cw", "DGenContraction"), ("lo", "Q")];
const F_EV: &[(&str, &str)] = &[("cw", "DGenContraction"), ("hi", "Q"), ("lo", "Q")];
const F_TAIL: &[(&str, &str)] = &[("coeff", "Q"), ("cw", "DGenContraction"), ("rate", "Q")];

/// The DtmcContraction family's rows of the claimed roster
/// (concatenated at registration — provider.rs). Registration order
/// is part of the seam surface: append at the end, never reorder.
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "qtsl_dtmc_genform_contraction",
        F_CW,
        RelKind::Dgc(DgcKind::Genform),
    ),
    (
        "qtsl_dgc_partial_lo",
        F_PARTIAL,
        RelKind::Dgc(DgcKind::PartialLo),
    ),
    (
        "qtsl_dgc_ev_bracket",
        F_EV,
        RelKind::Dgc(DgcKind::EvBracket),
    ),
    (
        "qtsl_dgc_survival_tail",
        F_TAIL,
        RelKind::Dgc(DgcKind::SurvivalTail),
    ),
    ("qtsl_dgc_z_one", F_CW, RelKind::Dgc(DgcKind::ZOne)),
];

/// A decoded contraction witness at the pure core's grain, over a
/// dense local state indexing `0..ns` (the walk's own, minted from
/// the decoded alphabet).
#[derive(Debug, Clone)]
pub struct DgcQuery {
    pub ns: usize,
    /// Absolute horizon (the DP's step count).
    pub horizon: usize,
    /// Anchor offset (deterministic prologue length; absent = 0).
    pub offset: usize,
    /// The contraction rate.
    pub c: QQ,
    /// `(state, V)` — the stored certificate component; the SUPPORT of
    /// this list is the alive region (membership is storage, never
    /// inference). At most one entry per state (P-FUN is the
    /// decoder's business; the core treats a duplicate as a caller
    /// bug).
    pub weights: Vec<(usize, QQ)>,
    /// `(src, dst) → p`, stored rows only (the completion diagonal is
    /// structure, applied during the walk).
    pub rows: Vec<(usize, usize, QQ)>,
    /// `state → mass`, the chain's dinit rows.
    pub init: Vec<(usize, QQ)>,
}

/// A decided violation — the named reason behind an `Ok(false)`
/// verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DgcViolation {
    /// The transfer inequality refuted at a region state (the
    /// completed kernel's weighted one-step sum exceeds `c·V`).
    Transfer { x: usize },
    /// A claim bound violated against its recomputed value (`lo`
    /// above the exact partial sum, `hi` below the warranted
    /// assembly, a tail rate outside `[c, 1)`, a negative tail
    /// coefficient, a coefficient below the warranted envelope).
    Claim,
}

impl std::fmt::Display for DgcViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DgcViolation::Transfer { x } => {
                write!(f, "transfer inequality refuted at region state {x}")
            }
            DgcViolation::Claim => write!(f, "claim bound violated"),
        }
    }
}

/// Three-valued outcome: `Ok(Ok(()))` holds, `Ok(Err(v))` decided
/// false, `Err(reason)` refused.
pub type DgcOut = Result<Result<(), DgcViolation>, String>;

// ---------------------------------------------------------------------
// The shared core
// ---------------------------------------------------------------------

/// The recomputed common substrate every relation of the family reads:
/// the region view, the killed-on-exit evolution, and the derived
/// constants.
pub struct DgcCore {
    /// `state → V` on the region (dense over `0..ns`, `None` = not in
    /// the region).
    pub v_of: Vec<Option<QQ>>,
    /// `surv[t] = P[T > t]` for `t = 0..=horizon`.
    pub survivals: Vec<QQ>,
    /// Weighted alive mass at the horizon.
    pub w: QQ,
    /// `min_A V` (the derived conversion's denominator; the region is
    /// nonempty by the face grammar, so the minimum exists).
    pub min_v: QQ,
    /// Whether the transfer inequality held at every region state
    /// under the completed kernel (a violation carries the state).
    pub transfer: Result<(), DgcViolation>,
}

/// Row lawfulness at the chain grain, recomputed (the dev-oracle
/// posture: violations REFUSE — a sub-stochastic stored group has no
/// sound first-moment reading, so no claim of this family verdicts
/// over one): probabilities in `(0, 1]`, each present source group
/// summing to exactly one, init masses in `(0, 1]` summing to exactly
/// one.
fn check_rows_lawful(q: &DgcQuery) -> Result<(), String> {
    use std::cmp::Ordering::*;
    let zero = QQ::zero();
    let one = QQ::one();
    let mut group: HashMap<usize, QQ> = HashMap::new();
    for (src, _dst, p) in &q.rows {
        if p.cmp_qq(&zero) != Greater || p.cmp_qq(&one) == Greater {
            return Err(format!(
                "stored probability at source {src} outside (0, 1] — the stored \
                 grain identifies zero with absence, refusing"
            ));
        }
        let acc = group.entry(*src).or_insert_with(QQ::zero);
        *acc = acc.add(p);
    }
    for (src, tot) in &group {
        if tot.cmp_qq(&one) != Equal {
            return Err(format!(
                "source {src}: stored masses do not sum to 1 — truncation has no \
                 sound first-moment reading, refusing"
            ));
        }
    }
    let mut init_tot = QQ::zero();
    for (_s, m) in &q.init {
        if m.cmp_qq(&zero) != Greater || m.cmp_qq(&one) == Greater {
            return Err("dinit mass outside (0, 1] — refusing".into());
        }
        init_tot = init_tot.add(m);
    }
    if init_tot.cmp_qq(&one) != Equal {
        return Err("dinit masses do not sum to 1 — refusing".into());
    }
    Ok(())
}

/// Recompute the shared core. Refusals: rate range, empty region,
/// unlawful rows, re-entry, budget. The transfer verdict is CARRIED
/// (not short-circuited) so every caller applies it at its own tier.
pub fn dgc_core(q: &DgcQuery) -> Result<DgcCore, String> {
    use std::cmp::Ordering::*;
    let zero = QQ::zero();
    let one = QQ::one();

    // Rate range [0, 1] (the species' own range row, mirrored:
    // negative rates are not generally sound for the contraction
    // induction; rates above one are outside the species).
    if q.c.cmp_qq(&zero) == Less {
        return Err("contraction rate c < 0 — outside the species' range, refusing".into());
    }
    if q.c.cmp_qq(&one) == Greater {
        return Err("contraction rate c > 1 — outside the species' range, refusing".into());
    }

    if q.ns > DGC_MAX_STATES {
        return Err("state alphabet beyond the budget — refusing".into());
    }

    // The WHOLE budget, charged up front from lengths alone (nothing
    // has run yet, so exhaustion is a controlled refusal, never a
    // grind): every stage of this core — the lawfulness pass, the
    // region build, the no-re-entry scan, the one-pass transfer
    // recompute, each evolution step (which allocates and totals ns
    // cells, not merely the region), and the horizon readout — costs
    // a bounded number of passes over at most `rows + ns` cells, so
    // the charge is `(horizon + 1) · (rows + ns)` with the per-stage
    // constant folded into the cap's sizing. The `+ 1` floors the
    // formula at horizon zero: the one-time recomputes are charged
    // even when the evolution takes no steps.
    let per_pass = q.rows.len().saturating_add(q.ns);
    if per_pass.saturating_mul(q.horizon.saturating_add(1)) > DGC_MAX_WORK {
        return Err(
            "(horizon + 1) × (stored rows + states) beyond the work budget — \
             refusing the whole claim"
                .into(),
        );
    }

    check_rows_lawful(q)?;

    // The region: dweight support, dense view.
    if q.weights.is_empty() {
        return Err("empty alive region (no dweight rows) — nothing to certify, refusing".into());
    }
    let mut v_of: Vec<Option<QQ>> = vec![None; q.ns];
    for (s, v) in &q.weights {
        if *s >= q.ns {
            return Err("dweight row cites a state outside the alphabet — refusing".into());
        }
        if v_of[*s].replace(v.clone()).is_some() {
            return Err(
                "two dweight rows share one (cw, state) key — ambiguous (P-FUN \
                 territory), refusing"
                    .into(),
            );
        }
    }
    let min_v = q
        .weights
        .iter()
        .map(|(_, v)| v.clone())
        .reduce(|a, b| if b.cmp_qq(&a) == Less { b } else { a })
        .expect("nonempty region");

    // No re-entry: a stored row from outside the region into it would
    // break the killed-on-exit reading (mass could come back).
    for (src, dst, p) in &q.rows {
        if *src >= q.ns || *dst >= q.ns {
            return Err("stored row cites a state outside the alphabet — refusing".into());
        }
        if v_of[*src].is_none() && v_of[*dst].is_some() && p.cmp_qq(&zero) == Greater {
            return Err(format!(
                "re-entry: stored row from non-region state {src} into region state \
                 {dst} — the regional reading is refuted, refusing"
            ));
        }
    }

    // Transfer under the completed kernel, at every region state:
    // rowful — the stored row sum over region destinations; rowless —
    // the completion self-loop (LHS = V(x), which honors the c = 1
    // subsumption face and refutes decay at c < 1 by itself).
    // ONE row pass accumulates the regional sums, then one region
    // pass compares — O(rows + ns), inside the charged budget (the
    // per-region-state row rescan this replaced was quadratic and
    // uncharged).
    let has_rows: Vec<bool> = {
        let mut v = vec![false; q.ns];
        for (src, _, _) in &q.rows {
            v[*src] = true;
        }
        v
    };
    let mut lhs_of: Vec<Option<QQ>> = v_of
        .iter()
        .map(|v| v.as_ref().map(|_| QQ::zero()))
        .collect();
    for (src, dst, p) in &q.rows {
        if lhs_of[*src].is_none() {
            continue; // off-region source: exit-side rows carry no LHS
        }
        if let Some(vd) = &v_of[*dst] {
            let add = p.mul(vd);
            let slot = lhs_of[*src].as_mut().expect("region slot");
            *slot = slot.add(&add);
        }
    }
    let mut transfer: Result<(), DgcViolation> = Ok(());
    for (x, vx) in v_of.iter().enumerate() {
        let Some(vx) = vx else { continue };
        let lhs = if has_rows[x] {
            lhs_of[x].as_ref().expect("region slot").clone()
        } else {
            vx.clone()
        };
        if lhs.cmp_qq(&q.c.mul(vx)) == Greater {
            transfer = Err(DgcViolation::Transfer { x });
            break;
        }
    }

    // The killed-on-exit evolution, region-restricted (autonomous
    // under no-re-entry): m_0 = dinit|A; each step walks the stored
    // region→region rows plus the completion diagonal at rowless
    // region states; mass to exits (region→non-region rows) drops.
    let mut m: Vec<QQ> = vec![QQ::zero(); q.ns];
    for (s, mass) in &q.init {
        if *s >= q.ns {
            return Err("dinit row cites a state outside the alphabet — refusing".into());
        }
        if v_of[*s].is_some() {
            m[*s] = m[*s].add(mass);
        }
    }
    let mut survivals: Vec<QQ> = Vec::with_capacity(q.horizon + 1);
    let total = |m: &[QQ]| m.iter().fold(QQ::zero(), |a, b| a.add(b));
    survivals.push(total(&m));
    for _t in 0..q.horizon {
        let mut next = vec![QQ::zero(); q.ns];
        for (src, dst, p) in &q.rows {
            if v_of[*src].is_none() || m[*src].is_zero() {
                continue;
            }
            if v_of[*dst].is_some() {
                next[*dst] = next[*dst].add(&m[*src].mul(p));
            }
        }
        for s in 0..q.ns {
            if v_of[s].is_some() && !has_rows[s] && !m[s].is_zero() {
                next[s] = next[s].add(&m[s]);
            }
        }
        m = next;
        survivals.push(total(&m));
    }
    let mut w = QQ::zero();
    for (s, vx) in v_of.iter().enumerate() {
        if let Some(vx) = vx {
            if !m[s].is_zero() {
                w = w.add(&m[s].mul(vx));
            }
        }
    }

    Ok(DgcCore {
        v_of,
        survivals,
        w,
        min_v,
        transfer,
    })
}

// ---------------------------------------------------------------------
// Shared demands the claims spend
// ---------------------------------------------------------------------

/// The offset prologue determinism: `k ≤ horizon`, and for `k > 0`
/// the total surviving mass at step `k − 1` equals one (all initial
/// mass inside the region and none exited yet). `k = 0` is vacuous.
fn check_offset(q: &DgcQuery, core: &DgcCore) -> Result<(), String> {
    use std::cmp::Ordering::*;
    if q.offset > q.horizon {
        return Err(format!(
            "anchor offset {} beyond horizon {} — refusing",
            q.offset, q.horizon
        ));
    }
    if q.offset > 0 && core.survivals[q.offset - 1].cmp_qq(&QQ::one()) != Equal {
        return Err(format!(
            "anchor offset {} claims a deterministic prologue but the surviving \
             mass at step {} is not 1 — refusing",
            q.offset,
            q.offset - 1
        ));
    }
    Ok(())
}

/// The weighted-to-bare conversion: a positive region minimum (the
/// derived reciprocal `κ = 1/min_A V` exists). Claims that read bare
/// region mass off weighted decay spend this; a non-positive minimum
/// has no conversion (a negative weight satisfies contraction
/// vacuously while holding mass — the committed countermodel's
/// shape), so those claims refuse.
fn check_conversion(core: &DgcCore) -> Result<(), String> {
    use std::cmp::Ordering::*;
    if core.min_v.cmp_qq(&QQ::zero()) != Greater {
        return Err(
            "no weighted-to-bare conversion: the region's minimum weight is not \
             positive (κ = 1/min V undefined) — refusing"
                .into(),
        );
    }
    Ok(())
}

/// The geometric assembly's rate demand: `c < 1` strictly.
fn check_c_strict(q: &DgcQuery, what: &str) -> Result<(), String> {
    use std::cmp::Ordering::*;
    if q.c.cmp_qq(&QQ::one()) != Less {
        return Err(format!("{what} needs c < 1 (geometric decay) — refusing"));
    }
    Ok(())
}

/// `L`: the exact partial survival sum over `[offset, horizon)`.
fn partial_sum(q: &DgcQuery, core: &DgcCore) -> QQ {
    core.survivals[q.offset..q.horizon]
        .iter()
        .fold(QQ::zero(), |a, b| a.add(b))
}

/// `x^e` by square-and-multiply (exact).
fn qq_pow(x: &QQ, mut e: usize) -> QQ {
    let mut acc = QQ::one();
    let mut base = x.clone();
    while e > 0 {
        if e & 1 == 1 {
            acc = acc.mul(&base);
        }
        base = base.mul(&base);
        e >>= 1;
    }
    acc
}

// ---------------------------------------------------------------------
// The five relations (pure faces; the decoder feeds them)
// ---------------------------------------------------------------------

/// R18 — the strengthened generator-form demand: shape/range demands,
/// no re-entry, per-region-state contraction under the completed
/// kernel, and the offset prologue determinism whenever the witness
/// declares one. (The cross-face same-chain check is the decoder's:
/// it needs the row context, not the pure query.)
pub fn check_dgc_genform(q: &DgcQuery) -> DgcOut {
    let core = dgc_core(q)?;
    // The R18 demand includes the positive region minimum (the
    // species derives the conversion constant for every consumer;
    // a witness with no conversion is refused at the demand).
    check_conversion(&core)?;
    // Conservative reading of "where a partial/EV claim spends it":
    // a DECLARED offset is checked at the demand whenever positive —
    // the pure grain cannot see which claims ride the container, and
    // refusing a declared-but-indeterministic prologue is safe in
    // the refusal direction (the per-claim recomputes check it again
    // where spent).
    if q.offset > 0 {
        check_offset(q, &core)?;
    }
    Ok(core.transfer)
}

/// `qtsl_dgc_partial_lo {cw, lo}` — `lo ≤ L`, the exact partial
/// survival sum with the prologue subtracted.
pub fn check_dgc_partial_lo(q: &DgcQuery, lo: &QQ) -> DgcOut {
    use std::cmp::Ordering::*;
    let core = dgc_core(q)?;
    if let Err(v) = core.transfer {
        return Ok(Err(v));
    }
    check_offset(q, &core)?;
    let l = partial_sum(q, &core);
    if lo.cmp_qq(&l) == Greater {
        return Ok(Err(DgcViolation::Claim));
    }
    Ok(Ok(()))
}

/// `qtsl_dgc_ev_bracket {cw, lo, hi}` — `lo ≤ L` and
/// `hi ≥ L + κ·W/(1−c)`, division-free by cross-multiplication:
/// `(hi − L) · (1−c) · min_V ≥ W` (both factors positive after the
/// demands).
pub fn check_dgc_ev_bracket(q: &DgcQuery, lo: &QQ, hi: &QQ) -> DgcOut {
    use std::cmp::Ordering::*;
    let core = dgc_core(q)?;
    // The conversion refusals PRECEDE the transfer verdict (the dev
    // oracle's own order: a non-positive weight refuses before the
    // transfer sweep runs — a claim without a conversion is
    // undecidable for this species, not false).
    check_c_strict(q, "the EV assembly")?;
    check_conversion(&core)?;
    if let Err(v) = core.transfer {
        return Ok(Err(v));
    }
    check_offset(q, &core)?;
    let l = partial_sum(q, &core);
    if lo.cmp_qq(&l) == Greater {
        return Ok(Err(DgcViolation::Claim));
    }
    let one_minus = QQ::one().sub(&q.c);
    let lhs = hi.sub(&l).mul(&one_minus).mul(&core.min_v);
    if lhs.cmp_qq(&core.w) == Less {
        return Ok(Err(DgcViolation::Claim));
    }
    Ok(Ok(()))
}

/// `qtsl_dgc_survival_tail {cw, coeff, rate}` — the envelope
/// `P[T > n] ≤ coeff · rate^n` for all `n ≥ horizon`, discharged as
/// `coeff ≥ 0`, `rate ∈ [c, 1)`, and
/// `coeff · rate^horizon · min_V ≥ W` (the `n = horizon` instance of
/// `coeff · rate^n ≥ κ·W·c^{n−horizon}`, which dominates every later
/// `n` once `rate ≥ c`).
pub fn check_dgc_survival_tail(q: &DgcQuery, coeff: &QQ, rate: &QQ) -> DgcOut {
    use std::cmp::Ordering::*;
    let core = dgc_core(q)?;
    // Conversion refusals precede the transfer verdict (see the EV
    // bracket's note).
    check_c_strict(q, "the survival tail")?;
    check_conversion(&core)?;
    if let Err(v) = core.transfer {
        return Ok(Err(v));
    }
    // The range demands (the theory's own tail-range report,
    // mirrored): 0 ≤ coeff, 0 ≤ rate < 1.
    if coeff.cmp_qq(&QQ::zero()) == Less {
        return Ok(Err(DgcViolation::Claim));
    }
    if rate.cmp_qq(&QQ::zero()) == Less || rate.cmp_qq(&QQ::one()) != Less {
        return Ok(Err(DgcViolation::Claim));
    }
    // Fully-drained face: W(T) = 0 forces S(n) = 0 for every n ≥ T
    // (the contraction caps κ·W(n) ≤ κ·W(T)·c^{n−T} = 0), so any
    // lawful envelope holds — including rates below c.
    if core.w.is_zero() {
        return Ok(Ok(()));
    }
    // Live-mass face: the envelope must dominate κ·W(T)·c^{n−T} at
    // every n ≥ T, which needs rate ≥ c and the n = T instance.
    if rate.cmp_qq(&q.c) == Less {
        return Ok(Err(DgcViolation::Claim));
    }
    let lhs = coeff.mul(&qq_pow(rate, q.horizon)).mul(&core.min_v);
    if lhs.cmp_qq(&core.w) == Less {
        return Ok(Err(DgcViolation::Claim));
    }
    Ok(Ok(()))
}

/// `qtsl_dgc_z_one {cw}` — termination mass exactly one: geometric
/// decay (`0 ≤ c < 1`, transfer green), a positive conversion, and
/// every region state's stored rows summing to one (a rowless region
/// state holds its mass forever — its completion self-loop already
/// refutes the transfer at `c < 1`, but the demand is stated here so
/// the relation's meaning does not lean on that coincidence). No
/// initial-containment demand: with `T` the first exit from the
/// region, mass that starts OUTSIDE has `T = 0` — it terminates
/// trivially, and only the region mass needs the decay argument.
pub fn check_dgc_z_one(q: &DgcQuery) -> DgcOut {
    let core = dgc_core(q)?;
    // Conversion refusals precede the transfer verdict (see the EV
    // bracket's note).
    check_c_strict(q, "the termination row")?;
    check_conversion(&core)?;
    if let Err(v) = core.transfer {
        return Ok(Err(v));
    }
    // Row-mass-one at every region state: lawfulness already refused
    // sub-unit GROUPS; what remains is the rowless region state.
    let has_rows: Vec<bool> = {
        let mut v = vec![false; q.ns];
        for (src, _, _) in &q.rows {
            v[*src] = true;
        }
        v
    };
    for (s, vx) in core.v_of.iter().enumerate() {
        if vx.is_some() && !has_rows[s] {
            return Err(format!(
                "region state {s} has no stored rows — the completion holds its \
                 mass forever, the termination row is unwarranted, refusing"
            ));
        }
    }
    Ok(Ok(()))
}

// ---------------------------------------------------------------------
// Vocabulary
// ---------------------------------------------------------------------

/// Field positions of a record-domain fun, resolved BY NAME at
/// vocabulary build (never assumed positional) — the DtmcAbsorb
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

/// The DtmcContraction vocabulary, pinned at vocabulary resolution
/// (names select, shapes verify, identities pin). Spans the chain
/// species' stored grain (`dprob`/`dinit`/`DState/dtmc`), the witness
/// species' own declarations, the DEFERRED-face pins (attributes
/// whose presence refuses this event: the score face and — while the
/// closure still declares them — the template/pattern fields), and
/// the cross-face absorption anchor where the closure carries both
/// species.
#[derive(Debug, Clone)]
pub struct DgcVocab {
    witness_anchor: Chid,
    witness_horizon: Chid,
    witness_offset: Chid,
    witness_c: Chid,
    dstate_dtmc: Chid,
    dprob: Chid,
    dprob_pos: FieldPos,
    dinit: Chid,
    dinit_pos: FieldPos,
    dweight: Chid,
    dweight_pos: FieldPos,
    /// Attribute funs whose PRESENCE on a witness refuses this event
    /// (deferred-safe-fail), each with the face named: the score
    /// field always; the template/pattern fields while the closure
    /// declares them (a closure without those declarations makes the
    /// faces unrepresentable — the stronger posture — and the pins
    /// are simply absent).
    deferred: Vec<(Chid, &'static str)>,
    /// The `dprofile` keyed relation, when declared — pattern-face
    /// data; any row on a witness refuses this event.
    dprofile: Option<Chid>,
    /// `DAbsQuery/anchor`, when the closure carries the absorption
    /// species — the R18 cross-face same-chain check reads it.
    dabs_anchor: Option<Chid>,
}

/// Build the DtmcContraction vocabulary for the named
/// `DGenContraction` sort. `Err` → the family is not claimed
/// (C-ORACLE safe-fail; reason recorded on the provider's vocabulary
/// notes).
pub fn build_dgc_vocab(indices: &[&TheoryIndex], witness_sort: Chid) -> Result<DgcVocab, String> {
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
    let record_decl = |name: &str,
                       want: &[(&str, &dyn Fn(&SortKey) -> bool)],
                       want_cod: Option<SortKey>|
     -> Result<(Chid, FieldPos), String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational {
                return Err(format!("`{name}`: expected a fun declaration"));
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
    // A deferred-face pin: resolved when declared, shape-unchecked
    // (its whole job is presence detection for the refusal).
    let opt_fun = |name: &str| -> Option<Chid> {
        indices
            .iter()
            .find_map(|index| index.fun(name))
            .map(|d| d.chid)
    };

    let (witness_anchor, wa_cod) = attr("DGenContraction/anchor", witness_sort)?;
    let SortKey::Elem(dstate_sort) = wa_cod else {
        return Err("`DGenContraction/anchor` does not land in an element sort".into());
    };
    let (witness_horizon, wh_cod) = attr("DGenContraction/horizon", witness_sort)?;
    if wh_cod != SortKey::Ground(Ground::Nat) {
        return Err("`DGenContraction/horizon` does not land in Nat".into());
    }
    let (witness_offset, wo_cod) = attr("DGenContraction/offset", witness_sort)?;
    if wo_cod != SortKey::Ground(Ground::Nat) {
        return Err("`DGenContraction/offset` does not land in Nat".into());
    }
    let (witness_c, wc_cod) = attr("DGenContraction/c", witness_sort)?;
    if wc_cod != SortKey::Ground(Ground::Q) {
        return Err("`DGenContraction/c` does not land in Q".into());
    }
    let (dstate_dtmc, dd_cod) = attr("DState/dtmc", dstate_sort)?;
    if !matches!(dd_cod, SortKey::Elem(_)) {
        return Err("`DState/dtmc` does not land in an element sort".into());
    }
    let is_state = |s: &SortKey| *s == SortKey::Elem(dstate_sort);
    let is_witness = |s: &SortKey| *s == SortKey::Elem(witness_sort);
    let is_elem = |s: &SortKey| matches!(s, SortKey::Elem(_));
    let (dprob, dprob_pos) = record_decl(
        "dprob",
        &[("src", &is_state), ("dst", &is_state)],
        Some(SortKey::Ground(Ground::Q)),
    )?;
    let (dinit, dinit_pos) = record_decl(
        "dinit",
        &[("chain", &is_elem), ("state", &is_state)],
        Some(SortKey::Ground(Ground::Q)),
    )?;
    let (dweight, dweight_pos) = record_decl(
        "dweight",
        &[("cw", &is_witness), ("state", &is_state)],
        Some(SortKey::Ground(Ground::Q)),
    )?;
    let mut deferred: Vec<(Chid, &'static str)> = Vec::new();
    for (name, face) in [
        (
            "DGenContraction/score",
            "the soft-score face (present score refuses this event — \
             deferred-safe-fail)",
        ),
        ("DGenContraction/gamma", "the 1-D template face"),
        ("DGenContraction/tM", "the 1-D template face"),
        ("DGenContraction/pattern", "the pattern face"),
        ("DGenContraction/pdim", "the pattern face"),
        ("DGenContraction/pup", "the pattern face"),
        ("DGenContraction/box", "the pattern face"),
        ("DGenContraction/growth", "the pattern face"),
    ] {
        if let Some(chid) = opt_fun(name) {
            deferred.push((chid, face));
        }
    }
    let dprofile = opt_fun("dprofile");
    // Cross-face: the absorption species' anchor, when aboard.
    let dabs_anchor = opt_fun("DAbsQuery/anchor");
    Ok(DgcVocab {
        witness_anchor,
        witness_horizon,
        witness_offset,
        witness_c,
        dstate_dtmc,
        dprob,
        dprob_pos,
        dinit,
        dinit_pos,
        dweight,
        dweight_pos,
        deferred,
        dprofile,
        dabs_anchor,
    })
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
    /// duplication both refuse (P-FUN posture at the attribute
    /// grain).
    fn need_attr(&self, subject: u32, fun: Chid, what: &str) -> Result<&'a Value, EvalError> {
        self.opt_attr(subject, fun, what)?.ok_or_else(|| {
            ctx_err(
                self.name,
                format!("element {subject} has no `{what}` row — structure undecidable"),
            )
        })
    }

    /// The at-most-one attribute row (absence lawful — the field's
    /// default applies; duplication refuses).
    fn opt_attr(
        &self,
        subject: u32,
        fun: Chid,
        what: &str,
    ) -> Result<Option<&'a Value>, EvalError> {
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
}

/// Decode one contraction witness from the row context: anchor →
/// chain, the chain's state alphabet, stored outcome/init/weight
/// rows, the deferred-face refusals — refusing on everything the
/// context cannot decide.
fn decode_witness(d: &Decoder, v: &DgcVocab, witness: u32) -> Result<DgcQuery, EvalError> {
    let name = d.name;
    let rows = d.rows;

    // --- deferred faces refuse before anything else ---------------------
    for (chid, face) in &v.deferred {
        if d.opt_attr(witness, *chid, "deferred-face attribute")?
            .is_some()
        {
            return Err(ctx_err(
                name,
                format!("{face} is not realized this event — refusing, never guessing"),
            ));
        }
    }
    if let Some(dprof) = &v.dprofile {
        for row in rows.arg_rows(witness) {
            if row.fun == *dprof {
                return Err(ctx_err(
                    name,
                    "dprofile rows (the pattern face) are not realized this event — \
                     refusing, never guessing"
                        .into(),
                ));
            }
        }
    }

    // --- anchor → chain ---------------------------------------------------
    let anchor_val = d
        .need_attr(witness, v.witness_anchor, "DGenContraction/anchor")?
        .clone();
    let anchor = d.elem(&anchor_val)?;
    let horizon_val = d
        .need_attr(witness, v.witness_horizon, "DGenContraction/horizon")?
        .clone();
    let horizon_n = d.nat_lit(&horizon_val, "DGenContraction/horizon")?;
    let offset_n = match d.opt_attr(witness, v.witness_offset, "DGenContraction/offset")? {
        Some(val) => d.nat_lit(val, "DGenContraction/offset")?,
        None => 0,
    };
    let c_val = d
        .need_attr(witness, v.witness_c, "DGenContraction/c")?
        .clone();
    let c = d.q_lit(&c_val, "DGenContraction/c")?;
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
    if state_elems.len() > DGC_MAX_STATES {
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
            continue;
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

    // --- the stored certificate component (witness-keyed; the
    // (cw, state) key is functional) ---------------------------------------
    let w_cw_pos = v.dweight_pos.of("cw");
    let w_state_pos = v.dweight_pos.of("state");
    let mut weights: Vec<(usize, QQ)> = Vec::new();
    let mut seen_w: HashSet<u32> = HashSet::new();
    for row in rows.arg_rows(witness) {
        if row.fun != v.dweight {
            continue;
        }
        if d.elem(&row.args[w_cw_pos])? != witness {
            continue;
        }
        let state_elem = d.elem(&row.args[w_state_pos])?;
        let Some(s_idx) = ids.get(&state_elem) else {
            return Err(ctx_err(
                name,
                "a weight row cites a state outside the witness chain's decoded \
                 state set — identity undecidable, refusing"
                    .into(),
            ));
        };
        if !seen_w.insert(state_elem) {
            return Err(ctx_err(
                name,
                "two weight rows share one (cw, state) key — ambiguous (P-FUN \
                 territory), refusing"
                    .into(),
            ));
        }
        weights.push((*s_idx, d.q_lit(&row.value, "dweight value")?));
    }

    // --- budgets ------------------------------------------------------------
    let horizon = usize::try_from(horizon_n)
        .map_err(|_| ctx_err(name, "horizon beyond the work budget — refusing".into()))?;
    let offset = usize::try_from(offset_n)
        .map_err(|_| ctx_err(name, "offset beyond the work budget — refusing".into()))?;
    // The same whole-budget formula the core charges (from lengths
    // alone; the `+ 1` floors it at horizon zero so the one-time
    // recomputes are always charged).
    let per_pass = out_rows.len().saturating_add(ns);
    if per_pass.saturating_mul(horizon.saturating_add(1)) > DGC_MAX_WORK {
        return Err(ctx_err(
            name,
            "(horizon + 1) × (stored rows + states) beyond the work budget — \
             refusing the whole claim"
                .into(),
        ));
    }

    Ok(DgcQuery {
        ns,
        horizon,
        offset,
        c,
        weights,
        rows: out_rows,
        init,
    })
}

/// The R18 cross-face same-chain check: every absorption query in the
/// row context must anchor the SAME chain as the witness — a
/// container carrying both species over two chains has no shared
/// co-binding reading (the data-plane review's finding), so the
/// demand refuses it.
fn check_cross_face(d: &Decoder, v: &DgcVocab, witness_chain: u32) -> Result<(), EvalError> {
    let Some(dabs_anchor) = v.dabs_anchor else {
        return Ok(());
    };
    let name = d.name;
    let rows = d.rows;
    for subject in rows.subject_elems() {
        for row in rows.attrs(subject) {
            if row.fun != dabs_anchor {
                continue;
            }
            let q_anchor = d.elem(&row.value)?;
            let chain_val = d.need_attr(q_anchor, v.dstate_dtmc, "DState/dtmc")?.clone();
            if d.elem(&chain_val)? != witness_chain {
                return Err(ctx_err(
                    name,
                    "an absorption query in this container anchors a DIFFERENT chain \
                     than the contraction witness — no shared co-binding reading, \
                     refusing"
                        .into(),
                ));
            }
        }
    }
    for row in rows.external_subject_rows() {
        if row.fun == dabs_anchor {
            return Err(ctx_err(
                name,
                "an absorption query with an external subject shares this container — \
                 its chain is undecidable here, refusing"
                    .into(),
            ));
        }
    }
    Ok(())
}

/// Render a pure-face outcome into the dispatch's
/// `Result<bool, EvalError>`.
fn out(name: &str, o: DgcOut) -> Result<bool, EvalError> {
    match o {
        Ok(Ok(())) => Ok(true),
        Ok(Err(_)) => Ok(false),
        Err(refuse) => Err(ctx_err(name, refuse)),
    }
}

/// The DtmcContraction family's evaluation. Args in wire field
/// order — `genform`/`z_one`: `(cw)`; `partial_lo`: `(cw, lo)`;
/// `ev_bracket`: `(cw, hi, lo)`; `survival_tail`:
/// `(coeff, cw, rate)`.
pub(crate) fn eval_dgc(
    name: &str,
    v: &DgcVocab,
    kind: DgcKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let d = Decoder { name, rows };
    match kind {
        DgcKind::Genform => {
            let witness = d.elem(args[0])?;
            let q = decode_witness(&d, v, witness)?;
            // The cross-face check needs the witness's chain element:
            // re-read it (cheap — two attribute rows).
            let anchor_val = d
                .need_attr(witness, v.witness_anchor, "DGenContraction/anchor")?
                .clone();
            let anchor = d.elem(&anchor_val)?;
            let chain_val = d.need_attr(anchor, v.dstate_dtmc, "DState/dtmc")?.clone();
            let chain = d.elem(&chain_val)?;
            check_cross_face(&d, v, chain)?;
            out(name, check_dgc_genform(&q))
        }
        DgcKind::PartialLo => {
            let witness = d.elem(args[0])?;
            let lo = d.q_lit(args[1], "lo")?;
            let q = decode_witness(&d, v, witness)?;
            out(name, check_dgc_partial_lo(&q, &lo))
        }
        DgcKind::EvBracket => {
            let witness = d.elem(args[0])?;
            let hi = d.q_lit(args[1], "hi")?;
            let lo = d.q_lit(args[2], "lo")?;
            let q = decode_witness(&d, v, witness)?;
            out(name, check_dgc_ev_bracket(&q, &lo, &hi))
        }
        DgcKind::SurvivalTail => {
            let coeff = d.q_lit(args[0], "coeff")?;
            let witness = d.elem(args[1])?;
            let rate = d.q_lit(args[2], "rate")?;
            let q = decode_witness(&d, v, witness)?;
            out(name, check_dgc_survival_tail(&q, &coeff, &rate))
        }
        DgcKind::ZOne => {
            let witness = d.elem(args[0])?;
            let q = decode_witness(&d, v, witness)?;
            out(name, check_dgc_z_one(&q))
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

    /// The die-paradox chain as a contraction witness: states
    /// 0 = alive (V = 1), 1 = acc, 2 = rej (both exits, unweighted);
    /// rows alive → acc 1/6, alive → alive 1/3, alive → rej 1/2. The
    /// region sum at the one region state is (1/3)·1 = 1/3 ≤ c·1, so
    /// c = 1/3 is the eigen-tight rate.
    fn die(horizon: usize, c: QQ) -> DgcQuery {
        DgcQuery {
            ns: 3,
            horizon,
            offset: 0,
            c,
            weights: vec![(0, q(1, 1))],
            rows: vec![(0, 1, q(1, 6)), (0, 0, q(1, 3)), (0, 2, q(1, 2))],
            init: vec![(0, q(1, 1))],
        }
    }

    /// Canonical values at horizon 10, c = 1/3: `surv[t] = (1/3)^t`,
    /// `L = (1 − (1/3)^10)·3/2 = 88573/59049·…` — recomputed here
    /// against the closed form; `W = (1/3)^10`, `κ = 1`.
    #[test]
    fn die_partial_and_ev_exact() {
        let dq = die(10, q(1, 3));
        // L = sum_{t<10} 3^-t = (3^10 - 1)/(2·3^9) = 29524/19683.
        let l = q(29524, 19683);
        assert!(check_dgc_partial_lo(&dq, &l).unwrap().is_ok());
        // one grain tighter refuses the claim (decided false).
        assert_eq!(
            check_dgc_partial_lo(&dq, &q(29525, 19683)).unwrap(),
            Err(DgcViolation::Claim)
        );
        // EV: warranted hi = L + κW/(1−c) = L + (1/3)^10·(3/2)
        //   = 29524/19683 + 3/(2·59049) = L + 1/39366.
        let hi = l.add(&q(1, 39366));
        assert!(check_dgc_ev_bracket(&dq, &l, &hi).unwrap().is_ok());
        let hi_tight = l.add(&q(1, 39367));
        assert_eq!(
            check_dgc_ev_bracket(&dq, &l, &hi_tight).unwrap(),
            Err(DgcViolation::Claim)
        );
        // tail: coeff·(1/3)^10 ≥ κW = (1/3)^10 — coeff = 1 is tight.
        assert!(check_dgc_survival_tail(&dq, &q(1, 1), &q(1, 3))
            .unwrap()
            .is_ok());
        assert_eq!(
            check_dgc_survival_tail(&dq, &q(59048, 59049), &q(1, 3)).unwrap(),
            Err(DgcViolation::Claim)
        );
        // z-one holds: rows total, init in region, c < 1, min V = 1.
        assert!(check_dgc_z_one(&dq).unwrap().is_ok());
        // genform holds at the tight rate and at the c = 1
        // subsumption face.
        assert!(check_dgc_genform(&dq).unwrap().is_ok());
        assert!(check_dgc_genform(&die(10, q(1, 1))).unwrap().is_ok());
    }

    /// Rate tightened past the spectral value: transfer refutes
    /// (decided FALSE, the claim tier), never a refusal.
    #[test]
    fn c_tighter_fails_transfer() {
        let dq = die(10, q(1, 4));
        assert_eq!(
            check_dgc_genform(&dq).unwrap(),
            Err(DgcViolation::Transfer { x: 0 })
        );
        assert_eq!(
            check_dgc_partial_lo(&dq, &q(0, 1)).unwrap(),
            Err(DgcViolation::Transfer { x: 0 })
        );
    }

    /// Negative and above-one rates refuse at the range demand.
    #[test]
    fn c_range_refuses() {
        assert!(check_dgc_genform(&die(10, q(-4, 5))).is_err());
        assert!(check_dgc_genform(&die(10, q(6, 5))).is_err());
    }

    /// The assembly demands c < 1: EV and tail refuse at c = 1 while
    /// genform (the subsumption face) holds.
    #[test]
    fn assembly_refuses_at_c_one() {
        let dq = die(10, q(1, 1));
        assert!(check_dgc_ev_bracket(&dq, &q(0, 1), &q(100, 1)).is_err());
        assert!(check_dgc_survival_tail(&dq, &q(100, 1), &q(1, 2)).is_err());
        assert!(check_dgc_z_one(&dq).is_err());
    }

    /// A zero (and a negative) region weight refuses the conversion
    /// claims — κ has no value — while the lemma-faithful demand
    /// tier is untouched. The negative-weight unit-self-loop shape
    /// (contraction satisfied, termination false) is the committed
    /// countermodel's checker face: z-one must never verdict on it.
    #[test]
    fn conversion_refuses_nonpositive_weights() {
        let mut dq = die(10, q(1, 3));
        dq.weights = vec![(0, q(0, 1))];
        assert!(check_dgc_ev_bracket(&dq, &q(0, 1), &q(100, 1)).is_err());
        assert!(check_dgc_survival_tail(&dq, &q(100, 1), &q(1, 2)).is_err());
        assert!(check_dgc_z_one(&dq).is_err());
        // The R18 demand itself carries the positive-minimum demand
        // (the species derives the conversion for every consumer).
        assert!(check_dgc_genform(&dq).is_err());
        // The countermodel shape: V = −1 at a unit self-loop, c = 1/2;
        // the transfer holds (−1 ≤ −1/2) and the mass never leaves.
        let cm = DgcQuery {
            ns: 1,
            horizon: 4,
            offset: 0,
            c: q(1, 2),
            weights: vec![(0, q(-1, 1))],
            rows: vec![(0, 0, q(1, 1))],
            init: vec![(0, q(1, 1))],
        };
        let core = dgc_core(&cm).expect("core computes");
        assert!(
            core.transfer.is_ok(),
            "contraction holds on the countermodel"
        );
        assert!(
            check_dgc_z_one(&cm).is_err(),
            "z-one must refuse, never verdict"
        );
        assert!(check_dgc_survival_tail(&cm, &q(1, 1), &q(1, 2)).is_err());
    }

    /// Re-entry refuses: a stored row from outside the region into it.
    #[test]
    fn reentry_refuses() {
        let mut dq = die(10, q(1, 3));
        dq.rows.push((1, 0, q(1, 1)));
        let e = check_dgc_genform(&dq).expect_err("re-entry refuses");
        assert!(e.contains("re-entry"), "{e}");
    }

    /// Offset semantics: beyond-horizon refuses; a non-deterministic
    /// prologue refuses; a genuinely deterministic one passes and
    /// shifts the partial sum.
    #[test]
    fn offset_prologue() {
        // Two-step chain: start → alive (deterministic), then the die.
        // States: 0 start (V 4/3 — the transfer at the start demands
        // V(0) ≥ V(1)/c, tight here), 1 alive (V 2/3), 2 acc, 3 rej.
        let mk = |offset: usize| DgcQuery {
            ns: 4,
            horizon: 11,
            offset,
            c: q(1, 2),
            weights: vec![(0, q(4, 3)), (1, q(2, 3))],
            rows: vec![
                (0, 1, q(1, 1)),
                (1, 2, q(1, 6)),
                (1, 1, q(1, 3)),
                (1, 3, q(1, 2)),
            ],
            init: vec![(0, q(1, 1))],
        };
        // offset 1: P[T > 0] = 1 (all mass at start, in-region).
        let dq = mk(1);
        assert!(check_dgc_genform(&dq).unwrap().is_ok());
        // L = sum_{t in [1, 11)} surv[t] = sum_{k<10} (1/3)^k = 29524/19683.
        let l = q(29524, 19683);
        assert!(check_dgc_partial_lo(&dq, &l).unwrap().is_ok());
        assert_eq!(
            check_dgc_partial_lo(&dq, &l.add(&q(1, 100000))).unwrap(),
            Err(DgcViolation::Claim)
        );
        // k = 2 is ALSO deterministic on this chain (the mass sits at
        // the alive state after one step; exits begin at step two) —
        // a legitimate witness, and the boundary case worth pinning.
        assert!(check_dgc_genform(&mk(2)).unwrap().is_ok());
        // offset-early: k = 3 claims P[T > 2] = 1 but surv[2] = 1/3
        // (the die's first exit already happened) — refuses.
        let early = mk(3);
        assert!(check_dgc_partial_lo(&early, &q(0, 1)).is_err());
        assert!(check_dgc_genform(&early).is_err());
        // offset beyond horizon refuses.
        let mut beyond = mk(1);
        beyond.offset = 99;
        assert!(check_dgc_partial_lo(&beyond, &q(0, 1)).is_err());
        // offset-dropped: k = 0 keeps the k = 1 EV upper bound, which
        // now sits below the warranted assembly (the prologue's
        // survival mass 1 joins L) — decided FALSE at the EV claim.
        let dropped = mk(0);
        // warranted hi at k = 1: L + κW/(1−c); κ = 1/(2/3) = 3/2,
        // W = (2/3)·(1/3)^10·… — recompute both sides via the checker:
        // the k = 1 tight hi ACCEPTS at k = 1 …
        let w = q(2, 3).mul(&q(1, 59049));
        let tight_hi_k1 = l.add(&w.mul(&q(3, 1))); // κ/(1−c) = (3/2)·2 = 3
        assert!(check_dgc_ev_bracket(&mk(1), &l, &tight_hi_k1)
            .unwrap()
            .is_ok());
        // … and FAILS at k = 0 (L grows by surv[0] = 1).
        assert_eq!(
            check_dgc_ev_bracket(&dropped, &l, &tight_hi_k1).unwrap(),
            Err(DgcViolation::Claim)
        );
    }

    /// The scale-doubled positive control: all weights doubled, claims
    /// unchanged — the κ-normalized assembly is scale-invariant.
    #[test]
    fn scale_doubled_accepts() {
        let mut dq = die(10, q(1, 3));
        dq.weights = vec![(0, q(2, 1))];
        let l = q(29524, 19683);
        let hi = l.add(&q(1, 39366));
        assert!(check_dgc_ev_bracket(&dq, &l, &hi).unwrap().is_ok());
        assert!(check_dgc_survival_tail(&dq, &q(1, 1), &q(1, 3))
            .unwrap()
            .is_ok());
    }

    /// ML4's checker face (labeled per review: an implementation
    /// differential, not a certificate mutant — no stored row can
    /// widen the emission scope, so the test pins the LOOP SOURCE):
    /// initial mass parked outside the region never enters any
    /// survival sum — the claims are decided over region mass only.
    #[test]
    fn ml4_emission_scope_is_region_only() {
        // Half the mass starts at an off-region absorbing state 3.
        let dq = DgcQuery {
            ns: 4,
            horizon: 10,
            offset: 0,
            c: q(1, 3),
            weights: vec![(0, q(1, 1))],
            rows: vec![(0, 1, q(1, 6)), (0, 0, q(1, 3)), (0, 2, q(1, 2))],
            init: vec![(0, q(1, 2)), (3, q(1, 2))],
        };
        // surv[0] = 1/2 (region mass only); a partial-lo counting the
        // off-region mass (as if surv[0] were 1) breaks.
        let core = dgc_core(&dq).expect("core computes");
        assert_eq!(core.survivals[0], q(1, 2));
        let l_region = q(29524, 39366); // half the die L
        assert!(check_dgc_partial_lo(&dq, &l_region).unwrap().is_ok());
        assert_eq!(
            check_dgc_partial_lo(&dq, &q(29525, 39366)).unwrap(),
            Err(DgcViolation::Claim)
        );
        // z-one HOLDS: mass starting outside the region has T = 0
        // (first exit) and terminates trivially — only region mass
        // needs the decay argument. (An earlier draft refused here;
        // the sealed fragment pins the exit-time reading.)
        assert!(check_dgc_z_one(&dq).unwrap().is_ok());
    }

    /// Budget refusal, never divergence.
    #[test]
    fn budget_refuses() {
        let dq = die(usize::MAX / 4, q(1, 3));
        assert!(check_dgc_genform(&dq).is_err());
    }

    /// The fully-drained tail face, exercised for real: strictly
    /// positive V with the killed mass GONE by the horizon
    /// (`W(T) = 0`) admits any lawful envelope — including rates
    /// BELOW c (the one deliberate generosity past the dev oracle,
    /// which failed `rate < gamma` unconditionally) — while the
    /// coefficient and rate range guards still bite first.
    #[test]
    fn drained_tail_face() {
        // One region state (V = 1) whose whole row exits: mass gone
        // after one step, W(2) = 0 exactly.
        let dq = DgcQuery {
            ns: 2,
            horizon: 2,
            offset: 0,
            c: q(1, 2),
            weights: vec![(0, q(1, 1))],
            rows: vec![(0, 1, q(1, 1))],
            init: vec![(0, q(1, 1))],
        };
        let core = dgc_core(&dq).expect("core computes");
        assert!(core.w.is_zero(), "the horizon mass is drained");
        assert!(core.transfer.is_ok(), "exits carry zero LHS");
        // rate < c with a nonnegative coefficient: ACCEPT.
        assert!(check_dgc_survival_tail(&dq, &q(1, 1), &q(1, 4))
            .unwrap()
            .is_ok());
        // … even a zero coefficient (S(n) = 0 ≤ 0 for n ≥ T).
        assert!(check_dgc_survival_tail(&dq, &q(0, 1), &q(1, 4))
            .unwrap()
            .is_ok());
        // The guards fire BEFORE the drained shortcut: a negative
        // coefficient and a negative rate each decide FALSE.
        assert_eq!(
            check_dgc_survival_tail(&dq, &q(-1, 1), &q(1, 4)).unwrap(),
            Err(DgcViolation::Claim)
        );
        assert_eq!(
            check_dgc_survival_tail(&dq, &q(1, 1), &q(-1, 4)).unwrap(),
            Err(DgcViolation::Claim)
        );
        // A rate at one stays outside the geometric contract.
        assert_eq!(
            check_dgc_survival_tail(&dq, &q(1, 1), &q(1, 1)).unwrap(),
            Err(DgcViolation::Claim)
        );
        // The LIVE face keeps the rate ≥ c demand: same chain one
        // step earlier (W(1) > 0... here the drain is at step 1, so
        // use horizon 0 where the initial region mass is live).
        let live = DgcQuery { horizon: 0, ..dq };
        assert_eq!(
            check_dgc_survival_tail(&live, &q(1, 1), &q(1, 4)).unwrap(),
            Err(DgcViolation::Claim),
            "live mass at the horizon still demands rate ≥ c"
        );
        assert!(check_dgc_survival_tail(&live, &q(1, 1), &q(1, 2))
            .unwrap()
            .is_ok());
    }

    /// The horizon-zero boundary: the one-time recomputes are charged
    /// even when the evolution takes no steps, so a row count past
    /// the cap REFUSES up front — no stage runs, no verdict forms.
    /// (Before the whole-budget repair the charged product was zero
    /// at horizon zero and the transfer recompute ran uncharged.)
    #[test]
    fn budget_refuses_at_horizon_zero_with_large_rows() {
        let n = DGC_MAX_WORK + 1;
        let dq = DgcQuery {
            ns: 3,
            horizon: 0,
            offset: 0,
            c: q(1, 3),
            weights: vec![(0, q(1, 1))],
            rows: vec![(0, 1, q(1, 2)); n],
            init: vec![(0, q(1, 1))],
        };
        let e = check_dgc_genform(&dq).expect_err("horizon-zero budget refuses");
        assert!(e.contains("work budget"), "{e}");
        let e = check_dgc_partial_lo(&dq, &q(0, 1)).expect_err("claims refuse identically");
        assert!(e.contains("work budget"), "{e}");
    }

    /// The off-region boundary: the charge counts STATES, not merely
    /// the region — a large alphabet of off-region states (each
    /// evolution step allocates and totals the dense vector) exhausts
    /// the budget even with a one-state region and a handful of rows.
    #[test]
    fn budget_refuses_on_large_off_region_alphabet() {
        // ns at the states cap (passing that gate), horizon sized so
        // (horizon + 1) · (rows + ns) just exceeds the work cap.
        let ns = DGC_MAX_STATES;
        let horizon = DGC_MAX_WORK / ns; // 64: (64+1)·(3+65536) > 2^22
        let dq = DgcQuery {
            ns,
            horizon,
            offset: 0,
            c: q(1, 3),
            weights: vec![(0, q(1, 1))],
            rows: vec![(0, 1, q(1, 6)), (0, 0, q(1, 3)), (0, 2, q(1, 2))],
            init: vec![(0, q(1, 1))],
        };
        let e = check_dgc_genform(&dq).expect_err("off-region alphabet budget refuses");
        assert!(e.contains("work budget"), "{e}");
    }
}
