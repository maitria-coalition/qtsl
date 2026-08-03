//! The SPDE moment-core family: the stochastic-heat / stochastic-
//! Burgers expected-energy certificates (rungs SW-m + S1) as
//! provider-discharged claims over sealed rows.
//!
//! Three relations, all recompute-from-primary-data (derived
//! quantities — rates `2·nu·k²`, mode floors `q_k/(2·nu·k²)`, the
//! covariance trace, exponential brackets — are recomputed HERE from
//! the declared spectrum at every discharge; the certificate never
//! stores them, so forging one is unrepresentable):
//!
//! - **`spdeClaimValid [c: QSpdeClaim]`** — the beta discipline: the
//!   claim's Itô-correction node satisfies `value = (1/2)·hess·tr(Q)`
//!   with `tr(Q) = Σ_k q_k` recomputed from the spectrum's driver
//!   rows (q-table well-formedness enforced: modes in `[1, rank]`,
//!   mode 0 silent, no duplicates, nonnegative weights, declared tail
//!   form `zero`); `beta = beta_jet + value`; `alpha >= 0`; and for
//!   `alpha > 0` the floor row exists and equals `beta/alpha` (for
//!   `alpha = 0` a floor row is a defect — no stray unchecked data).
//! - **`spdeTierWitnessValid [w: QTierWit]`** — the tier-(ii)/(iii)
//!   non-degeneracy witnesses: per live noise mode, a trajectory of
//!   second-moment enclosures `m_k(t) ∈ [floor_k·(1−S_hi),
//!   floor_k·(1−S_lo)]` with `S_N(x) = Σ_{j<=N} (−x)^j/j!` recomputed
//!   independently and demanded VERBATIM (alternating regime
//!   `0 < x = 2·nu·k²·t <= 1`; truncations odd-below/even-above),
//!   monotone along each trajectory, confined to `[0, floor_k]`;
//!   every live mode witnessed; the summed last lower brackets attain
//!   the declared fraction of the partial floor, and the partial
//!   floor never exceeds the certified functional floor.
//! - **`spdeSummedFloorValid [s: QSummedFloor]`** — the S1 two-sided
//!   summed-floor enclosures: common witness times, powered brackets
//!   `e^{-x} = (e^{-x/n})^n` at the CANONICAL minimal power
//!   `n = max(⌈x⌉, 1)`, per-mode and summed enclosures verbatim,
//!   strictly monotone sums confined below `F = Σ_k q_k/r_k`, width
//!   controlled, attainment at the last time — and the family's
//!   falsifier, the floor tie `F + deficit = floor` with the deficit
//!   `Σ_k q_k·(1/alpha − 1/r_k)` recomputed termwise-nonnegative.
//!   The tie pins the claim's beta chain against checker-rederived
//!   mode-law content: a consistent forgery through `hess`, the
//!   correction, `beta`, and the floor survives `spdeClaimValid` and
//!   dies here.
//!
//! Semantic authority: the SW-m / S1 rung classes of the SPDE lane's
//! Lean development (`SpdeRungSW.lean` and kin — the class-quantified
//! reading of every claim) and the derived-covariance theorems of the
//! qtsl adequacy stock (`Adequacy/PdeRows.lean`: trace as summed
//! diagonal, grouped Parseval, the divergent-plain-trace structural
//! refusal); the mtk producer surface (`spde_gen_kit`) derives the
//! same trace/floor quantities on the untrusted side, so producer and
//! checker meet at numbers neither stores.
//!
//! Verdict discipline (the crate's, verbatim from [`crate::miranda`]/
//! [`crate::enclosure`]): a decided violation is `Ok(false)`;
//! anything the row context cannot decide — missing or duplicated
//! field rows, unresolvable or ambiguous elements, non-`zero` tail
//! forms (their species arrive with their own arms), exhausted list
//! or degree budgets — REFUSES with a reason, never guessing.

use crate::atomic::elem_local;
use crate::error::EvalError;
use crate::qq::QQ;
use crate::roster::{EntryRow, RelKind, SpdeKind};
use crate::rowctx::{CertRows, CtorRow};
use crate::theory::{Chid, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use num_bigint::{BigInt, BigUint};
use std::cmp::Ordering;

/// The SPDE moment family's rows of the claimed roster (concatenated
/// at registration — provider.rs). Registration order is part of the
/// seam surface: append at the end, never reorder.
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "spdeClaimValid",
        &[("c", "QSpdeClaim")],
        RelKind::SpdeMoment(SpdeKind::Claim),
    ),
    (
        "spdeTierWitnessValid",
        &[("w", "QTierWit")],
        RelKind::SpdeMoment(SpdeKind::TierWit),
    ),
    (
        "spdeSummedFloorValid",
        &[("s", "QSummedFloor")],
        RelKind::SpdeMoment(SpdeKind::SummedFloor),
    ),
];

/// List-length budget: refusal beyond, never divergence (also the
/// cycle guard for cons chains).
pub const SPDE_MAX_LIST: usize = 1 << 16;
/// Bracket-truncation degree budget (the [`crate::enclosure`] bound).
pub const SPDE_MAX_DEGREE: u64 = 1 << 12;
/// Powered-bracket exponent budget.
pub const SPDE_MAX_POWER: u64 = 1 << 12;
/// Mode-index budget (`k² · nu` must stay exact in small integers'
/// comfort zone; no honest torus certificate is within sight of it).
pub const SPDE_MAX_MODE: u64 = 1 << 20;

// ---------------------------------------------------------------------
// The pinned vocabulary
// ---------------------------------------------------------------------

/// The family's resolved vocabulary: field and constructor identities,
/// name-selected once at construction and shape-verified (names
/// select, shapes verify, identities pin).
#[derive(Debug, Clone)]
pub struct SpdeMomentVocab {
    spec_drivers: Chid,
    spec_nu: Chid,
    spec_rank: Chid,
    spec_tail: Chid,
    tf_zero: Chid,
    tf_bracket: Chid,
    tf_divergent: Chid,
    qdl_nil: Chid,
    qdl_cons: Chid,
    drv_k: Chid,
    drv_q: Chid,
    corr_hess: Chid,
    corr_spec: Chid,
    corr_value: Chid,
    cl_alpha: Chid,
    cl_beta: Chid,
    cl_betajet: Chid,
    cl_corr: Chid,
    cl_floor: Chid,
    ts_mhi: Chid,
    ts_mlo: Chid,
    ts_nhi: Chid,
    ts_nlo: Chid,
    ts_t: Chid,
    qts_nil: Chid,
    qts_cons: Chid,
    mt_k: Chid,
    mt_samples: Chid,
    qmt_nil: Chid,
    qmt_cons: Chid,
    tw_claim: Chid,
    tw_fraction: Chid,
    tw_modes: Chid,
    tw_partialfloor: Chid,
    tw_sumlo: Chid,
    tm_k: Chid,
    tm_mhi: Chid,
    tm_mlo: Chid,
    tm_nhi: Chid,
    tm_nlo: Chid,
    tm_power: Chid,
    qtm_nil: Chid,
    qtm_cons: Chid,
    tr_modes: Chid,
    tr_sumhi: Chid,
    tr_sumlo: Chid,
    tr_t: Chid,
    qtr_nil: Chid,
    qtr_cons: Chid,
    sf_attain: Chid,
    sf_claim: Chid,
    sf_deficit: Chid,
    sf_fexact: Chid,
    sf_times: Chid,
    sf_widthbound: Chid,
}

/// A fun by name across the indices, its codomain verified against
/// the expected sort. `Err` → the family is not claimed
/// (declared-but-unbound, safe-fail).
fn find_ctor(indices: &[&TheoryIndex], name: &str, codomain: Chid) -> Result<Chid, String> {
    let mut found: Option<Chid> = None;
    for index in indices {
        for d in &index.funs {
            if d.name != name {
                continue;
            }
            if d.codomain != Some(SortKey::Elem(codomain)) {
                return Err(format!("`{name}` does not target the expected sort"));
            }
            match found {
                None => found = Some(d.chid),
                Some(f) if f == d.chid => {}
                Some(_) => return Err(format!("`{name}` is ambiguous across the indices")),
            }
        }
    }
    found.ok_or_else(|| format!("`{name}` not declared"))
}

/// Any fun by name (field identity; the caller knows its shape from
/// the declaring index — [`crate::formrows::find_field`] pins the
/// domain sort, which is the load-bearing half here).
fn field_of(indices: &[&TheoryIndex], name: &str, domain: Chid) -> Result<Chid, String> {
    crate::formrows::find_field(indices, name, domain)
}

/// Build the family vocabulary over the declared indices.
pub fn build_spdemoment_vocab(indices: &[&TheoryIndex]) -> Result<SpdeMomentVocab, String> {
    let spec = crate::formrows::find_sort(indices, "QSpdeSpec")?;
    let tailform = crate::formrows::find_sort(indices, "QTailForm")?;
    let dlist = crate::formrows::find_sort(indices, "QDriverList")?;
    let driver = crate::formrows::find_sort(indices, "QDriver")?;
    let corr = crate::formrows::find_sort(indices, "QItoCorr")?;
    let claim = crate::formrows::find_sort(indices, "QSpdeClaim")?;
    let sample = crate::formrows::find_sort(indices, "QTrajSample")?;
    let slist = crate::formrows::find_sort(indices, "QTrajSampleList")?;
    let mtraj = crate::formrows::find_sort(indices, "QModeTraj")?;
    let mlist = crate::formrows::find_sort(indices, "QModeTrajList")?;
    let tier = crate::formrows::find_sort(indices, "QTierWit")?;
    let tmrow = crate::formrows::find_sort(indices, "QTimeModeRow")?;
    let tmlist = crate::formrows::find_sort(indices, "QTimeModeList")?;
    let trow = crate::formrows::find_sort(indices, "QTimeRow")?;
    let trlist = crate::formrows::find_sort(indices, "QTimeRowList")?;
    let sfloor = crate::formrows::find_sort(indices, "QSummedFloor")?;

    Ok(SpdeMomentVocab {
        spec_drivers: field_of(indices, "QSpdeSpec/drivers", spec)?,
        spec_nu: field_of(indices, "QSpdeSpec/nu", spec)?,
        spec_rank: field_of(indices, "QSpdeSpec/rank", spec)?,
        spec_tail: field_of(indices, "QSpdeSpec/tail", spec)?,
        tf_zero: find_ctor(indices, "tfZero", tailform)?,
        tf_bracket: find_ctor(indices, "tfBracket", tailform)?,
        tf_divergent: find_ctor(indices, "tfDivergent", tailform)?,
        qdl_nil: find_ctor(indices, "qdlNil", dlist)?,
        qdl_cons: find_ctor(indices, "qdlCons", dlist)?,
        drv_k: field_of(indices, "QDriver/k", driver)?,
        drv_q: field_of(indices, "QDriver/q", driver)?,
        corr_hess: field_of(indices, "QItoCorr/hess", corr)?,
        corr_spec: field_of(indices, "QItoCorr/spec", corr)?,
        corr_value: field_of(indices, "QItoCorr/value", corr)?,
        cl_alpha: field_of(indices, "QSpdeClaim/alpha", claim)?,
        cl_beta: field_of(indices, "QSpdeClaim/beta", claim)?,
        cl_betajet: field_of(indices, "QSpdeClaim/betaJet", claim)?,
        cl_corr: field_of(indices, "QSpdeClaim/corr", claim)?,
        cl_floor: field_of(indices, "QSpdeClaim/floor", claim)?,
        ts_mhi: field_of(indices, "QTrajSample/mhi", sample)?,
        ts_mlo: field_of(indices, "QTrajSample/mlo", sample)?,
        ts_nhi: field_of(indices, "QTrajSample/nhi", sample)?,
        ts_nlo: field_of(indices, "QTrajSample/nlo", sample)?,
        ts_t: field_of(indices, "QTrajSample/t", sample)?,
        qts_nil: find_ctor(indices, "qtsNil", slist)?,
        qts_cons: find_ctor(indices, "qtsCons", slist)?,
        mt_k: field_of(indices, "QModeTraj/k", mtraj)?,
        mt_samples: field_of(indices, "QModeTraj/samples", mtraj)?,
        qmt_nil: find_ctor(indices, "qmtNil", mlist)?,
        qmt_cons: find_ctor(indices, "qmtCons", mlist)?,
        tw_claim: field_of(indices, "QTierWit/claim", tier)?,
        tw_fraction: field_of(indices, "QTierWit/fraction", tier)?,
        tw_modes: field_of(indices, "QTierWit/modes", tier)?,
        tw_partialfloor: field_of(indices, "QTierWit/partialFloor", tier)?,
        tw_sumlo: field_of(indices, "QTierWit/sumLo", tier)?,
        tm_k: field_of(indices, "QTimeModeRow/k", tmrow)?,
        tm_mhi: field_of(indices, "QTimeModeRow/mhi", tmrow)?,
        tm_mlo: field_of(indices, "QTimeModeRow/mlo", tmrow)?,
        tm_nhi: field_of(indices, "QTimeModeRow/nhi", tmrow)?,
        tm_nlo: field_of(indices, "QTimeModeRow/nlo", tmrow)?,
        tm_power: field_of(indices, "QTimeModeRow/power", tmrow)?,
        qtm_nil: find_ctor(indices, "qtmNil", tmlist)?,
        qtm_cons: find_ctor(indices, "qtmCons", tmlist)?,
        tr_modes: field_of(indices, "QTimeRow/modes", trow)?,
        tr_sumhi: field_of(indices, "QTimeRow/sumHi", trow)?,
        tr_sumlo: field_of(indices, "QTimeRow/sumLo", trow)?,
        tr_t: field_of(indices, "QTimeRow/t", trow)?,
        qtr_nil: find_ctor(indices, "qtrNil", trlist)?,
        qtr_cons: find_ctor(indices, "qtrCons", trlist)?,
        sf_attain: field_of(indices, "QSummedFloor/attainFraction", sfloor)?,
        sf_claim: field_of(indices, "QSummedFloor/claim", sfloor)?,
        sf_deficit: field_of(indices, "QSummedFloor/deficit", sfloor)?,
        sf_fexact: field_of(indices, "QSummedFloor/fexact", sfloor)?,
        sf_times: field_of(indices, "QSummedFloor/times", sfloor)?,
        sf_widthbound: field_of(indices, "QSummedFloor/widthBound", sfloor)?,
    })
}

// ---------------------------------------------------------------------
// Decode plumbing (refuse-vs-false discipline)
// ---------------------------------------------------------------------

/// `Ok(None)` = decided FALSE (a definite violation); `Ok(Some(v))` =
/// decoded; `Err` = refusal.
type DecRes<T> = Result<Option<T>, EvalError>;

fn ctx_err(name: &str, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.into(),
        index: 0,
        why,
    }
}

/// The unique field row `fun(e) = value` (missing/multiple = refusal).
fn sole_field<'a>(
    name: &str,
    rows: &'a CertRows,
    e: u32,
    fun: Chid,
    what: &str,
) -> Result<&'a CtorRow, EvalError> {
    let mut found: Option<&CtorRow> = None;
    for row in rows.arg_rows(e) {
        if row.fun != fun {
            continue;
        }
        if found.is_some() {
            return Err(ctx_err(
                name,
                format!("element {e} has multiple `{what}` rows — never picking"),
            ));
        }
        found = Some(row);
    }
    found.ok_or_else(|| {
        ctx_err(
            name,
            format!("element {e} has no `{what}` row — structure undecidable"),
        )
    })
}

/// Zero-or-one field row (the optional-floor idiom).
fn opt_field<'a>(
    name: &str,
    rows: &'a CertRows,
    e: u32,
    fun: Chid,
    what: &str,
) -> Result<Option<&'a CtorRow>, EvalError> {
    let mut found: Option<&CtorRow> = None;
    for row in rows.arg_rows(e) {
        if row.fun != fun {
            continue;
        }
        if found.is_some() {
            return Err(ctx_err(
                name,
                format!("element {e} has multiple `{what}` rows — never picking"),
            ));
        }
        found = Some(row);
    }
    Ok(found)
}

fn value_q(name: &str, row: &CtorRow, what: &str) -> Result<QQ, EvalError> {
    let Value::Lit(l) = &row.value else {
        return Err(ctx_err(
            name,
            format!("`{what}` value is not a literal cell"),
        ));
    };
    QQ::from_q_literal(l).ok_or_else(|| ctx_err(name, format!("`{what}` value is not a Q literal")))
}

fn value_nat(name: &str, row: &CtorRow, what: &str) -> Result<u64, EvalError> {
    let Value::Lit(l) = &row.value else {
        return Err(ctx_err(
            name,
            format!("`{what}` value is not a literal cell"),
        ));
    };
    let LiteralView::Nat(n) = l.view() else {
        return Err(ctx_err(
            name,
            format!("`{what}` value is not a Nat literal"),
        ));
    };
    Ok(n)
}

fn value_elem(name: &str, rows: &CertRows, row: &CtorRow, what: &str) -> Result<u32, EvalError> {
    match &row.value {
        Value::Ref(r) => rows
            .local(r)
            .ok_or_else(|| ctx_err(name, format!("`{what}` value is an external element ref"))),
        _ => Err(ctx_err(name, format!("`{what}` value is not an element"))),
    }
}

fn field_q(name: &str, rows: &CertRows, e: u32, fun: Chid, what: &str) -> Result<QQ, EvalError> {
    value_q(name, sole_field(name, rows, e, fun, what)?, what)
}

fn field_nat(name: &str, rows: &CertRows, e: u32, fun: Chid, what: &str) -> Result<u64, EvalError> {
    value_nat(name, sole_field(name, rows, e, fun, what)?, what)
}

fn field_elem(
    name: &str,
    rows: &CertRows,
    e: u32,
    fun: Chid,
    what: &str,
) -> Result<u32, EvalError> {
    let row = sole_field(name, rows, e, fun, what)?;
    value_elem(name, rows, row, what)
}

/// The unique constructor row producing `e` AMONG the given
/// constructor identities (an element that is also some field's
/// value legitimately has non-constructor producer rows — field rows
/// file by value too; those are filtered by identity here). Zero or
/// multiple matches = refusal — an unconstructed or ambiguous element
/// is undecidable.
fn sole_ctor<'a>(
    name: &str,
    rows: &'a CertRows,
    e: u32,
    allowed: &[Chid],
) -> Result<&'a CtorRow, EvalError> {
    let mut found: Option<&CtorRow> = None;
    for row in rows.producers(e) {
        if !allowed.contains(&row.fun) {
            continue;
        }
        if found.is_some() {
            return Err(ctx_err(
                name,
                format!("element {e} has multiple constructor rows — never picking"),
            ));
        }
        found = Some(row);
    }
    found.ok_or_else(|| {
        ctx_err(
            name,
            format!("element {e} has no constructor row in the expected roster"),
        )
    })
}

/// Walk a `nil`/`cons` chain: the head elements, in list order.
/// Record args are in bytewise field order — `head` then `tail`.
fn walk_list(
    name: &str,
    rows: &CertRows,
    mut list: u32,
    nil: Chid,
    cons: Chid,
    what: &str,
) -> Result<Vec<u32>, EvalError> {
    let mut out = Vec::new();
    loop {
        if out.len() > SPDE_MAX_LIST {
            return Err(ctx_err(
                name,
                format!("`{what}` list exceeds the length budget ({SPDE_MAX_LIST})"),
            ));
        }
        let ctor = sole_ctor(name, rows, list, &[nil, cons])?;
        if ctor.fun == nil {
            return Ok(out);
        }
        if ctor.args.len() != 2 {
            return Err(ctx_err(
                name,
                format!("`{what}` cons arity {}", ctor.args.len()),
            ));
        }
        let head = match &ctor.args[0] {
            Value::Ref(r) => rows
                .local(r)
                .ok_or_else(|| ctx_err(name, format!("`{what}` cons head is external")))?,
            _ => {
                return Err(ctx_err(
                    name,
                    format!("`{what}` cons head is not an element"),
                ))
            }
        };
        let tail = match &ctor.args[1] {
            Value::Ref(r) => rows
                .local(r)
                .ok_or_else(|| ctx_err(name, format!("`{what}` cons tail is external")))?,
            _ => {
                return Err(ctx_err(
                    name,
                    format!("`{what}` cons tail is not an element"),
                ))
            }
        };
        out.push(head);
        list = tail;
    }
}

// ---------------------------------------------------------------------
// Exact arithmetic
// ---------------------------------------------------------------------

fn qq(n: i64, d: u64) -> QQ {
    QQ::new(BigInt::from(n), BigUint::from(d))
}

fn le(a: &QQ, b: &QQ) -> bool {
    a.cmp_qq(b) != Ordering::Greater
}

fn lt(a: &QQ, b: &QQ) -> bool {
    a.cmp_qq(b) == Ordering::Less
}

fn is_pos(x: &QQ) -> bool {
    x.is_nonneg() && !x.is_zero()
}

/// `a / b` for `b > 0` (callers establish positivity first — rates,
/// alphas, powers; a nonpositive divisor here is a caller bug).
fn qq_div(a: &QQ, b: &QQ) -> QQ {
    debug_assert!(is_pos(b), "qq_div: nonpositive divisor");
    QQ::new(
        a.num() * BigInt::from(b.den().clone()),
        a.den() * b.num().magnitude(),
    )
}

/// `a / j` for `j >= 1`.
fn qq_div_nat(a: &QQ, j: u64) -> QQ {
    debug_assert!(j >= 1);
    QQ::new(a.num().clone(), a.den() * j)
}

/// `S_N(x) = Σ_{j=0}^{N} (−x)^j / j!` — the alternating exp-bracket
/// partial sum, term recurrence in exact rationals.
fn exp_neg_partial(x: &QQ, n: u64) -> QQ {
    let mut total = QQ::zero();
    let mut term = QQ::one();
    let neg_x = x.neg();
    for j in 0..=n {
        if j > 0 {
            term = qq_div_nat(&term.mul(&neg_x), j);
        }
        total = total.add(&term);
    }
    total
}

/// `b^e` by square-and-multiply (exact).
fn qq_pow(b: &QQ, mut e: u64) -> QQ {
    let mut base = b.clone();
    let mut acc = QQ::one();
    while e > 0 {
        if e & 1 == 1 {
            acc = acc.mul(&base);
        }
        e >>= 1;
        if e > 0 {
            base = base.mul(&base);
        }
    }
    acc
}

/// `⌈x⌉` for `x > 0`, refusal beyond the power budget.
fn ceil_pos(name: &str, x: &QQ) -> Result<u64, EvalError> {
    debug_assert!(is_pos(x));
    let num = x.num().magnitude().clone();
    let den = x.den().clone();
    let ceil = (&num + &den - BigUint::from(1u32)) / &den;
    u64::try_from(&ceil)
        .ok()
        .filter(|c| *c <= SPDE_MAX_POWER)
        .ok_or_else(|| {
            ctx_err(
                name,
                format!("powered-bracket exponent exceeds the budget ({SPDE_MAX_POWER})"),
            )
        })
}

// ---------------------------------------------------------------------
// Decoded views
// ---------------------------------------------------------------------

struct SpecData {
    nu: QQ,
    /// `(k, q_k)` in declared order; keys distinct, in `[1, rank]`,
    /// weights nonnegative.
    table: Vec<(u64, QQ)>,
}

impl SpecData {
    fn q_of(&self, k: u64) -> Option<&QQ> {
        self.table.iter().find(|(kk, _)| *kk == k).map(|(_, q)| q)
    }

    /// `r_k = 2·nu·k²` (`nu > 0`, `k >= 1` established at decode).
    fn rate(&self, k: u64) -> QQ {
        let k2 = QQ::from_int((k * k) as i64);
        self.nu.mul(&k2).mul(&qq(2, 1))
    }

    fn live_modes(&self) -> Vec<u64> {
        self.table
            .iter()
            .filter(|(_, q)| is_pos(q))
            .map(|(k, _)| *k)
            .collect()
    }
}

/// Decode + well-formedness of the spectrum. Decided violations →
/// `Ok(None)`; structural undecidability and non-`zero` tail forms →
/// refusal (the bracket/divergent arms are OUTSIDE this family's v0
/// scope — their species arrive with their own relations, and
/// guessing a trace under them would be exactly the silent-read the
/// constructor-required tail exists to forbid).
fn decode_spec(name: &str, v: &SpdeMomentVocab, rows: &CertRows, spec: u32) -> DecRes<SpecData> {
    let nu = field_q(name, rows, spec, v.spec_nu, "QSpdeSpec/nu")?;
    if !is_pos(&nu) {
        return Ok(None);
    }
    let rank = field_nat(name, rows, spec, v.spec_rank, "QSpdeSpec/rank")?;
    if rank > SPDE_MAX_MODE {
        return Err(ctx_err(
            name,
            format!("declared rank exceeds the mode budget ({SPDE_MAX_MODE})"),
        ));
    }
    let tail = field_elem(name, rows, spec, v.spec_tail, "QSpdeSpec/tail")?;
    let tail_ctor = sole_ctor(name, rows, tail, &[v.tf_zero, v.tf_bracket, v.tf_divergent])?;
    if tail_ctor.fun != v.tf_zero {
        return Err(ctx_err(
            name,
            "non-zero tail form: outside the v0 moment-core scope (bracket/divergent \
             arms arrive with their own species) — refusing, never reading a trace"
                .into(),
        ));
    }
    let dlist = field_elem(name, rows, spec, v.spec_drivers, "QSpdeSpec/drivers")?;
    let drivers = walk_list(name, rows, dlist, v.qdl_nil, v.qdl_cons, "drivers")?;
    let mut table: Vec<(u64, QQ)> = Vec::with_capacity(drivers.len());
    for d in drivers {
        let k = field_nat(name, rows, d, v.drv_k, "QDriver/k")?;
        let q = field_q(name, rows, d, v.drv_q, "QDriver/q")?;
        // Mode 0 noise kills the mean-zero class discipline; modes
        // beyond the declared rank, duplicates, and negative weights
        // are decided defects.
        if k == 0 || k > rank || !q.is_nonneg() {
            return Ok(None);
        }
        if table.iter().any(|(kk, _)| *kk == k) {
            return Ok(None);
        }
        table.push((k, q));
    }
    Ok(Some(SpecData { nu, table }))
}

struct ClaimData {
    alpha: QQ,
    floor: Option<QQ>,
    spec: SpecData,
}

/// Decode + verify the claim chain: q-table WF, the Itô-correction
/// recompute, the beta discipline, and the floor row. The chain is
/// re-verified by every relation that references the claim, so a
/// forged twin element (claimed by nothing) can never be substituted
/// unnoticed.
fn decode_claim(name: &str, v: &SpdeMomentVocab, rows: &CertRows, c: u32) -> DecRes<ClaimData> {
    let alpha = field_q(name, rows, c, v.cl_alpha, "QSpdeClaim/alpha")?;
    let beta = field_q(name, rows, c, v.cl_beta, "QSpdeClaim/beta")?;
    let beta_jet = field_q(name, rows, c, v.cl_betajet, "QSpdeClaim/betaJet")?;
    let corr = field_elem(name, rows, c, v.cl_corr, "QSpdeClaim/corr")?;
    let hess = field_q(name, rows, corr, v.corr_hess, "QItoCorr/hess")?;
    let value = field_q(name, rows, corr, v.corr_value, "QItoCorr/value")?;
    let spec_e = field_elem(name, rows, corr, v.corr_spec, "QItoCorr/spec")?;
    let Some(spec) = decode_spec(name, v, rows, spec_e)? else {
        return Ok(None);
    };

    // value = (1/2) · hess · tr(Q), the trace recomputed here.
    let trace = spec.table.iter().fold(QQ::zero(), |acc, (_, q)| acc.add(q));
    if value != qq(1, 2).mul(&hess).mul(&trace) {
        return Ok(None);
    }
    // beta = beta_jet + correction — the laundering gate.
    if beta != beta_jet.add(&value) {
        return Ok(None);
    }
    if !alpha.is_nonneg() {
        return Ok(None);
    }
    let floor_row = opt_field(name, rows, c, v.cl_floor, "QSpdeClaim/floor")?;
    let floor = match floor_row {
        Some(row) => Some(value_q(name, row, "QSpdeClaim/floor")?),
        None => None,
    };
    match (&floor, alpha.is_zero()) {
        // alpha = 0 with a floor row: stray unchecked data — a defect.
        (Some(_), true) => return Ok(None),
        // alpha > 0 without its floor row.
        (None, false) => return Ok(None),
        // alpha > 0: floor = beta / alpha, exactly.
        (Some(f), false) => {
            if *f != qq_div(&beta, &alpha) {
                return Ok(None);
            }
        }
        (None, true) => {}
    }
    Ok(Some(ClaimData { alpha, floor, spec }))
}

// ---------------------------------------------------------------------
// The three evaluators
// ---------------------------------------------------------------------

/// `spdeClaimValid [c]`.
pub(crate) fn eval_spde_claim_valid(
    name: &str,
    v: &SpdeMomentVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let c = elem_local(name, 0, args[0], rows)?;
    Ok(decode_claim(name, v, rows, c)?.is_some())
}

/// `spdeTierWitnessValid [w]`.
pub(crate) fn eval_spde_tier_witness_valid(
    name: &str,
    v: &SpdeMomentVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let w = elem_local(name, 0, args[0], rows)?;
    let claim_e = field_elem(name, rows, w, v.tw_claim, "QTierWit/claim")?;
    let Some(claim) = decode_claim(name, v, rows, claim_e)? else {
        return Ok(false);
    };
    // The tier witnesses tie to the rate claim: alpha > 0 with its
    // certified functional floor.
    let Some(func_floor) = &claim.floor else {
        return Ok(false);
    };
    if claim.alpha.is_zero() {
        return Ok(false);
    }
    let fraction = field_q(name, rows, w, v.tw_fraction, "QTierWit/fraction")?;
    if !is_pos(&fraction) {
        return Ok(false);
    }
    let spec = &claim.spec;

    let mlist = field_elem(name, rows, w, v.tw_modes, "QTierWit/modes")?;
    let modes = walk_list(name, rows, mlist, v.qmt_nil, v.qmt_cons, "trajectories")?;
    if modes.is_empty() {
        return Ok(false);
    }
    let mut witnessed: Vec<u64> = Vec::new();
    let mut partial_floor = QQ::zero();
    let mut sum_lo_last = QQ::zero();
    for m in modes {
        let k = field_nat(name, rows, m, v.mt_k, "QModeTraj/k")?;
        let Some(qk) = spec.q_of(k) else {
            return Ok(false); // trajectory mode not in the q-table
        };
        if witnessed.contains(&k) {
            return Ok(false);
        }
        witnessed.push(k);
        if !is_pos(qk) {
            return Ok(false); // noise-silent: not a noise-realizing witness
        }
        let rate = spec.rate(k);
        let mfloor = qq_div(qk, &rate);
        let slist = field_elem(name, rows, m, v.mt_samples, "QModeTraj/samples")?;
        let samples = walk_list(name, rows, slist, v.qts_nil, v.qts_cons, "samples")?;
        if samples.is_empty() {
            return Ok(false);
        }
        let mut prev_lo = qq(-1, 1);
        let mut prev_hi = qq(-1, 1);
        let mut last_lo = QQ::zero();
        for s in samples {
            let t = field_q(name, rows, s, v.ts_t, "QTrajSample/t")?;
            let n_lo = field_nat(name, rows, s, v.ts_nlo, "QTrajSample/nlo")?;
            let n_hi = field_nat(name, rows, s, v.ts_nhi, "QTrajSample/nhi")?;
            let d_lo = field_q(name, rows, s, v.ts_mlo, "QTrajSample/mlo")?;
            let d_hi = field_q(name, rows, s, v.ts_mhi, "QTrajSample/mhi")?;
            if n_hi > SPDE_MAX_DEGREE {
                return Err(ctx_err(
                    name,
                    format!("bracket truncation exceeds the degree budget ({SPDE_MAX_DEGREE})"),
                ));
            }
            let x = rate.mul(&t);
            // The alternating-bracket regime: 0 < x <= 1.
            if !is_pos(&x) || !le(&x, &QQ::one()) {
                return Ok(false);
            }
            // Truncations: odd below, even above, ordered.
            if n_lo % 2 != 1 || n_hi % 2 != 0 || n_hi < n_lo {
                return Ok(false);
            }
            let s_lo = exp_neg_partial(&x, n_lo); // <= e^{-x}
            let s_hi = exp_neg_partial(&x, n_hi); // >= e^{-x}
            let m_lo = mfloor.mul(&QQ::one().sub(&s_hi));
            let m_hi = mfloor.mul(&QQ::one().sub(&s_lo));
            // VERBATIM recompute agreement.
            if d_lo != m_lo || d_hi != m_hi {
                return Ok(false);
            }
            // Confinement to [0, mode floor].
            if !m_lo.is_nonneg() || !le(&m_lo, &m_hi) || !le(&m_hi, &mfloor) {
                return Ok(false);
            }
            // Monotone along the trajectory.
            if !le(&prev_lo, &m_lo) || !le(&prev_hi, &m_hi) {
                return Ok(false);
            }
            prev_lo = m_lo.clone();
            prev_hi = m_hi;
            last_lo = m_lo;
        }
        partial_floor = partial_floor.add(&mfloor);
        sum_lo_last = sum_lo_last.add(&last_lo);
    }
    // Every live noise mode carries a witness.
    for k in spec.live_modes() {
        if !witnessed.contains(&k) {
            return Ok(false);
        }
    }
    // The declared tier-(iii) aggregates, verbatim.
    let d_partial = field_q(name, rows, w, v.tw_partialfloor, "QTierWit/partialFloor")?;
    let d_sumlo = field_q(name, rows, w, v.tw_sumlo, "QTierWit/sumLo")?;
    if d_partial != partial_floor || d_sumlo != sum_lo_last {
        return Ok(false);
    }
    // Attainment, and the partial floor confined by the certified one.
    if lt(&sum_lo_last, &fraction.mul(&partial_floor)) {
        return Ok(false);
    }
    Ok(le(&partial_floor, func_floor))
}

/// `spdeSummedFloorValid [s]`.
pub(crate) fn eval_spde_summed_floor_valid(
    name: &str,
    v: &SpdeMomentVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let s = elem_local(name, 0, args[0], rows)?;
    let claim_e = field_elem(name, rows, s, v.sf_claim, "QSummedFloor/claim")?;
    let Some(claim) = decode_claim(name, v, rows, claim_e)? else {
        return Ok(false);
    };
    let Some(floor) = &claim.floor else {
        return Ok(false);
    };
    if claim.alpha.is_zero() {
        return Ok(false);
    }
    let spec = &claim.spec;

    // F = Σ_k q_k / r_k, recomputed.
    let mut f_exact = QQ::zero();
    for (k, q) in &spec.table {
        f_exact = f_exact.add(&qq_div(q, &spec.rate(*k)));
    }
    let d_fexact = field_q(name, rows, s, v.sf_fexact, "QSummedFloor/fexact")?;
    if d_fexact != f_exact {
        return Ok(false);
    }
    // The deficit, termwise nonnegative: Σ_k q_k (1/alpha − 1/r_k).
    let inv_alpha = qq_div(&QQ::one(), &claim.alpha);
    let mut deficit = QQ::zero();
    for (k, q) in &spec.table {
        let term = q.mul(&inv_alpha.sub(&qq_div(&QQ::one(), &spec.rate(*k))));
        if !term.is_nonneg() {
            return Ok(false); // a witness mode decays slower than the claimed rate
        }
        deficit = deficit.add(&term);
    }
    let d_deficit = field_q(name, rows, s, v.sf_deficit, "QSummedFloor/deficit")?;
    if d_deficit != deficit {
        return Ok(false);
    }
    // THE FALSIFIER: F + deficit = floor — the correction constant
    // pinned against checker-rederived mode-law content.
    if f_exact.add(&deficit) != *floor {
        return Ok(false);
    }

    let width_bound = field_q(name, rows, s, v.sf_widthbound, "QSummedFloor/widthBound")?;
    let attain = field_q(name, rows, s, v.sf_attain, "QSummedFloor/attainFraction")?;
    if !is_pos(&attain) {
        return Ok(false);
    }
    let live = spec.live_modes();

    let tlist = field_elem(name, rows, s, v.sf_times, "QSummedFloor/times")?;
    let times = walk_list(name, rows, tlist, v.qtr_nil, v.qtr_cons, "times")?;
    if times.is_empty() {
        return Ok(false);
    }
    let mut prev_t: Option<QQ> = None;
    let mut prev_slo = qq(-1, 1);
    let mut prev_shi = qq(-1, 1);
    let mut last_slo = QQ::zero();
    for row in times {
        let t = field_q(name, rows, row, v.tr_t, "QTimeRow/t")?;
        if let Some(pt) = &prev_t {
            if !lt(pt, &t) {
                return Ok(false); // common times not increasing
            }
        }
        prev_t = Some(t.clone());
        let mlist = field_elem(name, rows, row, v.tr_modes, "QTimeRow/modes")?;
        let mode_rows = walk_list(name, rows, mlist, v.qtm_nil, v.qtm_cons, "time modes")?;
        let mut seen: Vec<u64> = Vec::new();
        let mut s_lo = QQ::zero();
        let mut s_hi = QQ::zero();
        for mr in mode_rows {
            let k = field_nat(name, rows, mr, v.tm_k, "QTimeModeRow/k")?;
            let Some(qk) = spec.q_of(k) else {
                return Ok(false);
            };
            if seen.contains(&k) {
                return Ok(false);
            }
            seen.push(k);
            let rate = spec.rate(k);
            let mfloor = qq_div(qk, &rate);
            let x = rate.mul(&t);
            if !is_pos(&x) {
                return Ok(false);
            }
            // Canonical minimal power: n = max(⌈x⌉, 1).
            let n_canon = ceil_pos(name, &x)?.max(1);
            let power = field_nat(name, rows, mr, v.tm_power, "QTimeModeRow/power")?;
            if power != n_canon {
                return Ok(false);
            }
            let base = qq_div(&x, &QQ::from_int(power as i64));
            if !is_pos(&base) || !le(&base, &QQ::one()) {
                return Ok(false);
            }
            let n_lo = field_nat(name, rows, mr, v.tm_nlo, "QTimeModeRow/nlo")?;
            let n_hi = field_nat(name, rows, mr, v.tm_nhi, "QTimeModeRow/nhi")?;
            if n_hi > SPDE_MAX_DEGREE {
                return Err(ctx_err(
                    name,
                    format!("bracket truncation exceeds the degree budget ({SPDE_MAX_DEGREE})"),
                ));
            }
            if n_lo % 2 != 1 || n_hi % 2 != 0 || n_hi < n_lo {
                return Ok(false);
            }
            // Powered brackets: e^{-x} = (e^{-x/n})^n.
            let lo_e = qq_pow(&exp_neg_partial(&base, n_lo), power);
            let hi_e = qq_pow(&exp_neg_partial(&base, n_hi), power);
            let m_lo = mfloor.mul(&QQ::one().sub(&hi_e));
            let m_hi = mfloor.mul(&QQ::one().sub(&lo_e));
            let d_lo = field_q(name, rows, mr, v.tm_mlo, "QTimeModeRow/mlo")?;
            let d_hi = field_q(name, rows, mr, v.tm_mhi, "QTimeModeRow/mhi")?;
            if d_lo != m_lo || d_hi != m_hi {
                return Ok(false);
            }
            if !m_lo.is_nonneg() || !le(&m_lo, &m_hi) || !le(&m_hi, &mfloor) {
                return Ok(false);
            }
            s_lo = s_lo.add(&m_lo);
            s_hi = s_hi.add(&m_hi);
        }
        // Every live mode present at every common time.
        for k in &live {
            if !seen.contains(k) {
                return Ok(false);
            }
        }
        let d_slo = field_q(name, rows, row, v.tr_sumlo, "QTimeRow/sumLo")?;
        let d_shi = field_q(name, rows, row, v.tr_sumhi, "QTimeRow/sumHi")?;
        if d_slo != s_lo || d_shi != s_hi {
            return Ok(false);
        }
        // Strictly monotone sums.
        if !lt(&prev_slo, &s_lo) || !lt(&prev_shi, &s_hi) {
            return Ok(false);
        }
        prev_slo = s_lo.clone();
        prev_shi = s_hi.clone();
        // Confinement below F; width control.
        if !le(&s_hi, &f_exact) {
            return Ok(false);
        }
        if !le(&s_hi.sub(&s_lo), &width_bound) {
            return Ok(false);
        }
        last_slo = s_lo;
    }
    // Attainment at the last common time.
    Ok(!lt(&last_slo, &attain.mul(&f_exact)))
}

/// Family dispatch (the provider's arm).
pub(crate) fn eval_spdemoment(
    kind: SpdeKind,
    name: &str,
    v: &SpdeMomentVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    match kind {
        SpdeKind::Claim => eval_spde_claim_valid(name, v, args, rows),
        SpdeKind::TierWit => eval_spde_tier_witness_valid(name, v, args, rows),
        SpdeKind::SummedFloor => eval_spde_summed_floor_valid(name, v, args, rows),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The landed stochastic-heat constants: q₁ = 1/5, q₂ = 3/50,
    /// nu = 1/10 — tr(Q) = 13/50, r₁ = 1/5, r₂ = 4/5, floors 1 and
    /// 3/40, partial floor 43/40; the S1 ladder's own numbers.
    #[test]
    fn heat_constants_recompute() {
        let spec = SpecData {
            nu: qq(1, 10),
            table: vec![(1, qq(1, 5)), (2, qq(3, 50))],
        };
        assert_eq!(spec.rate(1), qq(1, 5));
        assert_eq!(spec.rate(2), qq(4, 5));
        let trace = spec.table.iter().fold(QQ::zero(), |acc, (_, q)| acc.add(q));
        assert_eq!(trace, qq(13, 50));
        let f: QQ = spec.table.iter().fold(QQ::zero(), |acc, (k, q)| {
            acc.add(&qq_div(q, &spec.rate(*k)))
        });
        assert_eq!(f, qq(43, 40));
        // floor = tr(Q)/(2 nu) = 13/10; deficit at alpha = 2 nu = 1/5:
        // q₁(5 − 5) + q₂(5 − 5/4) = (3/50)(15/4) = 9/40; 43/40 + 9/40
        // = 52/40 = 13/10 — the falsifier's tie, closed.
        let alpha = qq(1, 5);
        let inv_alpha = qq_div(&QQ::one(), &alpha);
        let deficit: QQ = spec.table.iter().fold(QQ::zero(), |acc, (k, q)| {
            acc.add(&q.mul(&inv_alpha.sub(&qq_div(&QQ::one(), &spec.rate(*k)))))
        });
        assert_eq!(deficit, qq(9, 40));
        assert_eq!(f.add(&deficit), qq(13, 10));
    }

    /// The bracket recurrence against the closed forms:
    /// S₁(x) = 1 − x; S₂(x) = 1 − x + x²/2; and the checker twin's
    /// independence anchor S₃(1/5) = 1 − 1/5 + 1/50 − 1/750.
    #[test]
    fn exp_neg_partial_closed_forms() {
        let x = qq(1, 5);
        assert_eq!(exp_neg_partial(&x, 0), QQ::one());
        assert_eq!(exp_neg_partial(&x, 1), qq(4, 5));
        assert_eq!(exp_neg_partial(&x, 2), qq(41, 50));
        assert_eq!(exp_neg_partial(&x, 3), qq(614, 750).add(&QQ::zero()));
        // Alternating bracket law at x ∈ (0, 1]: odd below even.
        assert!(lt(&exp_neg_partial(&x, 1), &exp_neg_partial(&x, 2)));
    }

    #[test]
    fn ceil_pos_and_pow() {
        assert_eq!(ceil_pos("t", &qq(4, 1)).unwrap(), 4);
        assert_eq!(ceil_pos("t", &qq(7, 2)).unwrap(), 4);
        assert_eq!(ceil_pos("t", &qq(1, 3)).unwrap(), 1);
        assert_eq!(qq_pow(&qq(2, 3), 3), qq(8, 27));
        assert_eq!(qq_pow(&qq(-1, 2), 2), qq(1, 4));
    }
}
