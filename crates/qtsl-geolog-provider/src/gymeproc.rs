//! The gymnasium e-process family: anytime-valid lower confidence
//! bounds on the expected episodic return of a fixed policy, certified
//! from an i.i.d. rollout ledger by a betting-martingale mixture
//! (Waudby-Smith–Ramdas style) with a randomized last look
//! (Ramdas–Manole Thm 5.4), as provider-discharged claims over sealed
//! rows.
//!
//! Two relations, both recompute-from-primary-data — the certificate
//! stores the protocol constants and the raw ledger, never a wealth
//! value, a scaled observable, or the bet grid (the grid is hardcoded
//! HERE, so a grid tamper is unrepresentable rather than discouraged):
//!
//! - **`gymEprocDetValid [c: QEprocCert]`** — the deterministic Ville
//!   verdict: the full mixture-wealth walk recomputed over the sealed
//!   ledger at the claimed boundary `m*`, in Q32.96 fixed point with
//!   every rounding directed DOWN (the computed wealth is a certified
//!   lower bound on the real wealth, so `wealth >= 1/alpha` soundly
//!   implies the real inequality), plus the raw-units bound tie
//!   `boundDet = kLo + m*·(kHi − kLo)/2^96` demanded exactly.
//! - **`gymEprocRandValid [c: QEprocCert]`** — the randomized last
//!   look: the same walk at `mRand >= mDet`, threshold scaled by the
//!   drawn `u` (`wealth >= u/alpha`, compared exactly in 256-bit
//!   integer arithmetic), plus the tie on the improved bound. The
//!   drawn-after-and-independent provenance of `u` is a declared
//!   protocol row (`QEprocLook/uProtocol`, demanded present) — that
//!   part is not machine-checkable, which is why the deterministic
//!   verdict is a separate relation discharged alongside.
//!
//! ## Claim classes (two, never mixed silently)
//!
//! With per-episode return `R` and scale constants `kLo < kHi`, the
//! class is an explicit constructor row (`QEprocCert/class`):
//!
//! - **`qecMinCap`**: observable `Y = min(R, kHi)`; `Y <= R` pointwise,
//!   so a lower confidence bound on `E[Y]` is one on `E[R]`. Soundness
//!   of the scaling then *requires* `R >= kLo` almost surely — the
//!   producer's range lemma. Every ledger entry is checked against it,
//!   and a violating entry REFUSES the certificate, carrying the entry
//!   (chunk, ordinal, exact value) as the lemma's refutation witness.
//! - **`qecClip(lo)`**: observable `Y = clip(R, lo, kHi)`; the claim is
//!   about the truncated mean `E[Y]` itself (weaker, model-gap-free);
//!   `lo == kLo` is demanded (tight scale) and no range lemma is
//!   consumed.
//!
//! ## Arithmetic (this family's whole trust surface)
//!
//! The scaled observable `y = (min/clip(R) − kLo)/(kHi − kLo) ∈ [0,1]`
//! is floored onto the 2^-96 grid in two exact integer steps, after an
//! exact floor of `R` onto the 2^-32 grid (`r32 = ⌊R·2^32⌋`, computed
//! from the sealed exact rational — equal, by monotonicity of floor,
//! to the same quantity computed from the IEEE-754 bits the ledger was
//! sampled in). The wealth walk multiplies per-episode factors
//! `1 + λ_j·(y − m)` over the hardcoded 16-entry dyadic bet grid
//! ([`GRID`]) with weights `2^-(j+1)`: factor terms are arithmetic
//! right-shifts (floor toward −∞), products floor at every multiply
//! ([`mul_shift96`]) and saturate DOWNWARD at [`CAP`] `= 2^120` (still
//! a lower bound; `CAP` exceeds every legal threshold since
//! `alphaInv <= 2^20`). The exact-rational mixture ([`wealth_exact`])
//! is the proptest anchor: `wealth_fp <= wealth_exact` always, so a
//! fixed-point ACCEPT implies the exact ACCEPT.
//!
//! The drawn `u` rides the container as an exact rational and is
//! demanded binary64-representable in the guarded range (`u >= 2^-60`,
//! dyadic denominator, numerator below 2^53) — the same value space
//! the sampling protocol drew from. The threshold comparison
//! `wealth·den(u) >= 2^96·alphaInv·num(u)` is scale-invariant in the
//! representation of `u`, so lowest-terms and IEEE
//! mantissa-and-exponent forms decide identically.
//!
//! Verdict discipline (the crate's): a decided violation — a wealth
//! walk landing below its threshold, a claimed bound failing its tie —
//! is `Ok(false)`; anything the row context cannot decide (missing or
//! duplicated field rows, malformed chunks, guard-range breaches, a
//! refuted range lemma) REFUSES with a reason, never guessing.

use crate::atomic::elem_local;
use crate::error::EvalError;
use crate::qq::QQ;
use crate::roster::{EntryRow, GymEprocKind, RelKind};
use crate::rowctx::{CertRows, CtorRow};
use crate::theory::{Chid, SortKey, TheoryIndex};
use geolog_envelope::cell::dtype;
use geolog_envelope::{Literal, LiteralView, Value};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};

/// The gymnasium e-process family's rows of the claimed roster
/// (concatenated at registration — provider.rs). Registration order is
/// part of the seam surface: append at the end, never reorder.
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "gymEprocDetValid",
        &[("c", "QEprocCert")],
        RelKind::GymEproc(GymEprocKind::Det),
    ),
    (
        "gymEprocRandValid",
        &[("c", "QEprocCert")],
        RelKind::GymEproc(GymEprocKind::Rand),
    ),
];

/// Q32.96 fixed point: the fractional width.
pub const FP: u32 = 96;
/// One, in Q32.96.
pub const ONE_FP: u128 = 1u128 << FP;
/// Saturation cap (downward): 2^120 = ONE << 24.
pub const CAP: u128 = ONE_FP << 24;
/// `alphaInv` ceiling keeping thresholds below CAP: 2^96·2^20 < 2^120.
pub const MAX_ALPHA_INV: u64 = 1 << 20;
/// Chunk-count budget: refusal beyond, never divergence.
pub const GYMEPROC_MAX_CHUNKS: usize = 1 << 20;

/// The hardcoded bet grid: `lambda_j = num_j / 2^(shift_j)` —
/// 15/16, 5/8, 15/32, 5/16, …, 5/1024 (alternating ratios 2/3 and
/// 3/4). Never carried by the certificate.
pub const GRID: [(u8, u8); 16] = [
    (15, 4),
    (5, 3),
    (15, 5),
    (5, 4),
    (15, 6),
    (5, 5),
    (15, 7),
    (5, 6),
    (15, 8),
    (5, 7),
    (15, 9),
    (5, 8),
    (15, 10),
    (5, 9),
    (15, 11),
    (5, 10),
];

// ---------------------------------------------------------------------
// The pinned vocabulary
// ---------------------------------------------------------------------

/// The family's resolved vocabulary: field and constructor identities,
/// name-selected once at construction and shape-verified (names
/// select, shapes verify, identities pin).
#[derive(Debug, Clone)]
pub struct GymEprocVocab {
    qec_mincap: Chid,
    qec_clip: Chid,
    alpha_inv: Chid,
    k_lo: Chid,
    k_hi: Chid,
    class: Chid,
    mdet_hi: Chid,
    mdet_lo: Chid,
    episodes: Chid,
    bound_det: Chid,
    ret_chunk: Chid,
    look: Chid,
    mrand_hi: Chid,
    mrand_lo: Chid,
    u: Chid,
    u_protocol: Chid,
    bound_rand: Chid,
}

/// A fun by name across the indices, its codomain verified against the
/// expected sort. `Err` → the family is not claimed
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

/// Build the family vocabulary over the declared indices.
pub fn build_gymeproc_vocab(indices: &[&TheoryIndex]) -> Result<GymEprocVocab, String> {
    let cert = crate::formrows::find_sort(indices, "QEprocCert")?;
    let class = crate::formrows::find_sort(indices, "QEprocClass")?;
    let look = crate::formrows::find_sort(indices, "QEprocLook")?;
    let f = |name: &str, domain: Chid| crate::formrows::find_field(indices, name, domain);
    Ok(GymEprocVocab {
        qec_mincap: find_ctor(indices, "qecMinCap", class)?,
        qec_clip: find_ctor(indices, "qecClip", class)?,
        alpha_inv: f("QEprocCert/alphaInv", cert)?,
        k_lo: f("QEprocCert/kLo", cert)?,
        k_hi: f("QEprocCert/kHi", cert)?,
        class: f("QEprocCert/class", cert)?,
        mdet_hi: f("QEprocCert/mDetHi", cert)?,
        mdet_lo: f("QEprocCert/mDetLo", cert)?,
        episodes: f("QEprocCert/episodes", cert)?,
        bound_det: f("QEprocCert/boundDet", cert)?,
        ret_chunk: f("QEprocCert/retChunk", cert)?,
        look: f("QEprocCert/look", cert)?,
        mrand_hi: f("QEprocLook/mRandHi", look)?,
        mrand_lo: f("QEprocLook/mRandLo", look)?,
        u: f("QEprocLook/u", look)?,
        u_protocol: f("QEprocLook/uProtocol", look)?,
        bound_rand: f("QEprocLook/boundRand", look)?,
    })
}

// ---------------------------------------------------------------------
// Row plumbing (refuse-vs-false discipline)
// ---------------------------------------------------------------------

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

fn value_lit<'a>(name: &str, row: &'a CtorRow, what: &str) -> Result<&'a Literal, EvalError> {
    match &row.value {
        Value::Lit(l) => Ok(l),
        _ => Err(ctx_err(
            name,
            format!("`{what}` value is not a literal cell"),
        )),
    }
}

fn field_nat(name: &str, rows: &CertRows, e: u32, fun: Chid, what: &str) -> Result<u64, EvalError> {
    let l = value_lit(name, sole_field(name, rows, e, fun, what)?, what)?;
    match l.view() {
        LiteralView::Nat(n) => Ok(n),
        _ => Err(ctx_err(
            name,
            format!("`{what}` value is not a Nat literal"),
        )),
    }
}

fn field_z(name: &str, rows: &CertRows, e: u32, fun: Chid, what: &str) -> Result<i64, EvalError> {
    let l = value_lit(name, sole_field(name, rows, e, fun, what)?, what)?;
    match l.view() {
        LiteralView::Z(v) => Ok(v),
        _ => Err(ctx_err(name, format!("`{what}` value is not a Z literal"))),
    }
}

fn field_qq(name: &str, rows: &CertRows, e: u32, fun: Chid, what: &str) -> Result<QQ, EvalError> {
    let l = value_lit(name, sole_field(name, rows, e, fun, what)?, what)?;
    QQ::from_q_literal(l).ok_or_else(|| ctx_err(name, format!("`{what}` value is not a Q literal")))
}

fn field_elem(
    name: &str,
    rows: &CertRows,
    e: u32,
    fun: Chid,
    what: &str,
) -> Result<u32, EvalError> {
    let row = sole_field(name, rows, e, fun, what)?;
    match &row.value {
        Value::Ref(r) => rows
            .local(r)
            .ok_or_else(|| ctx_err(name, format!("`{what}` value is an external element ref"))),
        _ => Err(ctx_err(name, format!("`{what}` value is not an element"))),
    }
}

/// The unique constructor row producing `e` among the given
/// constructor identities (zero or multiple = refusal).
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
            format!("element {e} has no roster constructor row — unresolvable"),
        )
    })
}

// ---------------------------------------------------------------------
// Fixed-point core (the workshop u4 checker's arithmetic, ported
// semantics-exact: every rounding directed DOWN)
// ---------------------------------------------------------------------

/// Full 256-bit product of two u128s, as (hi, lo).
fn mul256(a: u128, b: u128) -> (u128, u128) {
    const M64: u128 = (1u128 << 64) - 1;
    let (a1, a0) = (a >> 64, a & M64);
    let (b1, b0) = (b >> 64, b & M64);
    let ll = a0 * b0;
    let lh = a0 * b1;
    let hl = a1 * b0;
    let hh = a1 * b1;
    let (mid, c1) = lh.overflowing_add(hl);
    let (lo, c2) = ll.overflowing_add(mid << 64);
    let hi = hh + (mid >> 64) + (if c1 { 1u128 << 64 } else { 0 }) + (c2 as u128);
    (hi, lo)
}

/// (a · b) >> 96, floored. Callers keep a <= CAP (2^120), b < 2^97.
fn mul_shift96(a: u128, b: u128) -> u128 {
    let (hi, lo) = mul256(a, b);
    (hi << 32) | (lo >> 96)
}

/// Compare a·b vs c·d in 256 bits.
fn mul_cmp(a: u128, b: u128, c: u128, d: u128) -> core::cmp::Ordering {
    let x = mul256(a, b);
    let y = mul256(c, d);
    x.cmp(&y)
}

/// Sound (everywhere-floored, downward-saturating) lower bound on the
/// mixture wealth `K_n(m)` in Q32.96.
pub fn wealth_fp(ys: &[u128], m: u128) -> u128 {
    let mut mix: u128 = 0;
    for (j, &(num, shift)) in GRID.iter().enumerate() {
        let mut prod: u128 = ONE_FP;
        for &y in ys {
            let diff = y as i128 - m as i128; // in [-2^96, 2^96]
            let term = ((num as i128) * diff) >> shift; // floor toward -inf
            let factor = ((ONE_FP as i128) + term) as u128; // > 0 since lambda < 1
            prod = mul_shift96(prod, factor);
            if prod > CAP {
                prod = CAP; // downward saturation: still a lower bound
            }
            if prod == 0 {
                break;
            }
        }
        mix += prod >> (j + 1);
    }
    mix.min(CAP)
}

/// Exact mixture wealth over exact scaled observations (test anchor).
pub fn wealth_exact(ys: &[QQ], m: &QQ) -> QQ {
    let mut mix = QQ::zero();
    for (j, &(num, shift)) in GRID.iter().enumerate() {
        let lam = QQ::new(BigInt::from(num), BigUint::from(1u128 << shift));
        let w = QQ::new(BigInt::one(), BigUint::from(1u128 << (j + 1)));
        let mut prod = QQ::from_int(1);
        for y in ys {
            let factor = QQ::from_int(1).add(&lam.mul(&y.sub(m)));
            prod = prod.mul(&factor);
        }
        mix = mix.add(&w.mul(&prod));
    }
    mix
}

// ---------------------------------------------------------------------
// The scaled ledger
// ---------------------------------------------------------------------

/// `⌊(num/den)·2^32⌋` as i128, exact (Euclidean floor; den > 0). The
/// caller has already guarded `|num/den| <= 10^12`, so the result fits
/// comfortably in i128.
fn floor_x_2p32_q(num: &BigInt, den: &BigUint) -> i128 {
    let den = BigInt::from(den.clone());
    let scaled: BigInt = num << 32u32;
    let q = &scaled / &den;
    let r = &scaled % &den;
    let q = if !r.is_zero() && scaled.is_negative() {
        q - 1
    } else {
        q
    };
    i128::try_from(&q).expect("guarded magnitude fits i128")
}

/// Scaled observable `y` in Q0.96, floored, from the exact rational
/// return. `Err(Some(..))` carries a range-lemma refutation witness
/// message fragment; `Err(None)` a guard-range breach.
fn y_fp_from_q(
    num: &BigInt,
    den: &BigUint,
    k_lo: i64,
    k_hi: i64,
    clip: bool,
) -> Result<u128, Option<String>> {
    // |R| <= 10^12 (the workshop checker's guard, exact).
    let guard = BigInt::from(10u64.pow(12)) * BigInt::from(den.clone());
    if num.abs() > guard {
        return Err(None);
    }
    let g = (k_hi - k_lo) as u128; // k_lo < k_hi checked upstream
    let r32 = floor_x_2p32_q(num, den);
    let lo32 = (k_lo as i128) << 32;
    let hi32 = (k_hi as i128) << 32;
    let y32 = if clip {
        r32.clamp(lo32, hi32)
    } else {
        if r32 < lo32 {
            return Err(Some(format!(
                "return {num}/{den} below kLo={k_lo}: range lemma refuted by ledger"
            )));
        }
        r32.min(hi32)
    };
    // y = (y32 - lo32)/(G·2^32) in Q0.96, two exact steps (G < 2^48).
    let num2 = (y32 - lo32) as u128;
    let q1 = num2 / g; // <= 2^32
    let r1 = num2 % g; // < 2^48
    Ok((q1 << 64) + ((r1 << 64) / g))
}

/// The decoded protocol constants.
struct Protocol {
    alpha_inv: u64,
    k_lo: i64,
    k_hi: i64,
    /// `true` = clip class (`qecClip`, tight scale already verified);
    /// `false` = min-cap class (range lemma consumed).
    clip: bool,
    m_det: u128,
    episodes: u64,
    bound_det: QQ,
}

fn load_protocol(
    name: &str,
    v: &GymEprocVocab,
    rows: &CertRows,
    cert: u32,
) -> Result<Protocol, EvalError> {
    let alpha_inv = field_nat(name, rows, cert, v.alpha_inv, "QEprocCert/alphaInv")?;
    if !(2..=MAX_ALPHA_INV).contains(&alpha_inv) {
        return Err(ctx_err(
            name,
            format!("alphaInv {alpha_inv} outside [2, 2^20]"),
        ));
    }
    let k_lo = field_z(name, rows, cert, v.k_lo, "QEprocCert/kLo")?;
    let k_hi = field_z(name, rows, cert, v.k_hi, "QEprocCert/kHi")?;
    if k_lo >= k_hi || ((k_hi as i128 - k_lo as i128) as u128) >= (1u128 << 48) {
        return Err(ctx_err(name, format!("scale [{k_lo}, {k_hi}] malformed")));
    }
    let class_elem = field_elem(name, rows, cert, v.class, "QEprocCert/class")?;
    let class_row = sole_ctor(name, rows, class_elem, &[v.qec_mincap, v.qec_clip])?;
    let clip = if class_row.fun == v.qec_clip {
        let lo = match class_row.args.first() {
            Some(Value::Lit(l)) => match l.view() {
                LiteralView::Z(z) => z,
                _ => {
                    return Err(ctx_err(name, "qecClip argument is not a Z literal".into()));
                }
            },
            _ => return Err(ctx_err(name, "qecClip argument is not a literal".into())),
        };
        if lo != k_lo {
            return Err(ctx_err(
                name,
                format!("clip class requires kLo == clip lo (tight scale): {lo} vs {k_lo}"),
            ));
        }
        true
    } else {
        false
    };
    let m_hi = field_nat(name, rows, cert, v.mdet_hi, "QEprocCert/mDetHi")?;
    let m_lo = field_nat(name, rows, cert, v.mdet_lo, "QEprocCert/mDetLo")?;
    let m_det = ((m_hi as u128) << 64) | m_lo as u128;
    if m_det > ONE_FP {
        return Err(ctx_err(name, "mDet > 1".into()));
    }
    let episodes = field_nat(name, rows, cert, v.episodes, "QEprocCert/episodes")?;
    if episodes == 0 {
        return Err(ctx_err(name, "empty ledger (episodes = 0)".into()));
    }
    let bound_det = field_qq(name, rows, cert, v.bound_det, "QEprocCert/boundDet")?;
    Ok(Protocol {
        alpha_inv,
        k_lo,
        k_hi,
        clip,
        m_det,
        episodes,
        bound_det,
    })
}

/// Decode the chunked ledger and scale every entry (one pass;
/// range-witness refusals surface here, chunk and ordinal named).
fn scaled_ledger(
    name: &str,
    v: &GymEprocVocab,
    rows: &CertRows,
    cert: u32,
    p: &Protocol,
) -> Result<Vec<u128>, EvalError> {
    // Collect chunk rows keyed by index; duplicates refuse.
    let mut chunks: Vec<(u64, &Literal)> = Vec::new();
    for row in rows.attrs(cert) {
        if row.fun != v.ret_chunk {
            continue;
        }
        if row.args.len() != 2 {
            return Err(ctx_err(
                name,
                format!("retChunk row arity {} (want 2)", row.args.len()),
            ));
        }
        let idx = match &row.args[1] {
            Value::Lit(l) => match l.view() {
                LiteralView::Nat(n) => n,
                _ => return Err(ctx_err(name, "retChunk index is not a Nat literal".into())),
            },
            _ => return Err(ctx_err(name, "retChunk index is not a literal".into())),
        };
        let lit = match &row.value {
            Value::Lit(l) => l,
            _ => {
                return Err(ctx_err(
                    name,
                    "`QEprocCert/retChunk` value is not a literal cell".into(),
                ));
            }
        };
        if chunks.iter().any(|(i, _)| *i == idx) {
            return Err(ctx_err(name, format!("retChunk index {idx} duplicated")));
        }
        chunks.push((idx, lit));
    }
    if chunks.is_empty() {
        return Err(ctx_err(name, "no retChunk rows — ledger absent".into()));
    }
    if chunks.len() > GYMEPROC_MAX_CHUNKS {
        return Err(ctx_err(name, "chunk-count budget exhausted".into()));
    }
    chunks.sort_unstable_by_key(|(i, _)| *i);
    for (want, (got, _)) in chunks.iter().enumerate() {
        if *got != want as u64 {
            return Err(ctx_err(
                name,
                format!("retChunk indices not dense from 0 (missing {want})"),
            ));
        }
    }

    let mut ys: Vec<u128> = Vec::new();
    for (ci, lit) in &chunks {
        let tv = match lit.view() {
            LiteralView::TensorInline(tv) => tv,
            LiteralView::Tensor { .. } => {
                return Err(ctx_err(
                    name,
                    format!("retChunk {ci} is an identity envelope — entries not inline"),
                ));
            }
            _ => {
                return Err(ctx_err(name, format!("retChunk {ci} is not a tensor cell")));
            }
        };
        if tv.rank() != 1 {
            return Err(ctx_err(
                name,
                format!("retChunk {ci} rank {} (want 1)", tv.rank()),
            ));
        }
        if tv.elem_dtype() != dtype::Q {
            return Err(ctx_err(
                name,
                format!("retChunk {ci} element dtype is not Q"),
            ));
        }
        let count = tv.count();
        let mut seen = 0u64;
        for (ei, payload) in tv.entries().enumerate() {
            seen += 1;
            let l = Literal::from_parts(dtype::Q, payload.to_vec())
                .map_err(|e| ctx_err(name, format!("retChunk {ci} entry {ei}: {e}")))?;
            let (num, den) = match l.view() {
                LiteralView::Q { num, den } => (
                    BigInt::from_signed_bytes_le(num),
                    BigUint::from_bytes_le(den),
                ),
                _ => {
                    return Err(ctx_err(
                        name,
                        format!("retChunk {ci} entry {ei} is not a Q payload"),
                    ));
                }
            };
            match y_fp_from_q(&num, &den, p.k_lo, p.k_hi, p.clip) {
                Ok(y) => ys.push(y),
                Err(Some(witness)) => {
                    return Err(ctx_err(
                        name,
                        format!("range-witness at chunk {ci} entry {ei}: {witness}"),
                    ));
                }
                Err(None) => {
                    return Err(ctx_err(
                        name,
                        format!(
                            "retChunk {ci} entry {ei}: return magnitude beyond the 10^12 guard"
                        ),
                    ));
                }
            }
        }
        if seen != count {
            return Err(ctx_err(
                name,
                format!("retChunk {ci} entry stream short: {seen} of {count}"),
            ));
        }
    }
    if ys.len() as u64 != p.episodes {
        return Err(ctx_err(
            name,
            format!(
                "episode count mismatch: {} declared, {} ledger entries",
                p.episodes,
                ys.len()
            ),
        ));
    }
    Ok(ys)
}

/// The raw-units bound tie: `claimed == kLo + m·(kHi − kLo)/2^96`,
/// exact. A mismatch is a decided violation (false), never a refusal.
fn bound_tie(k_lo: i64, k_hi: i64, m: u128, claimed: &QQ) -> bool {
    let num =
        BigInt::from(k_lo) * BigInt::from(ONE_FP) + BigInt::from(m) * BigInt::from(k_hi - k_lo);
    let expected = QQ::new(num, BigUint::from(ONE_FP));
    claimed.cmp_qq(&expected) == core::cmp::Ordering::Equal
}

// ---------------------------------------------------------------------
// Evaluation
// ---------------------------------------------------------------------

pub(crate) fn eval_gymeproc(
    k: GymEprocKind,
    name: &str,
    v: &GymEprocVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    if args.len() != 1 {
        return Err(EvalError::Arity {
            name: name.into(),
            expected: 1,
            found: args.len(),
        });
    }
    let cert = elem_local(name, 0, args[0], rows)?;
    let p = load_protocol(name, v, rows, cert)?;
    let ys = scaled_ledger(name, v, rows, cert, &p)?;
    let thr = ONE_FP
        .checked_mul(p.alpha_inv as u128)
        .expect("alphaInv <= 2^20");

    match k {
        GymEprocKind::Det => {
            let l_det = wealth_fp(&ys, p.m_det);
            if l_det < thr {
                return Ok(false);
            }
            Ok(bound_tie(p.k_lo, p.k_hi, p.m_det, &p.bound_det))
        }
        GymEprocKind::Rand => {
            let look = field_elem(name, rows, cert, v.look, "QEprocCert/look")?;
            let m_hi = field_nat(name, rows, look, v.mrand_hi, "QEprocLook/mRandHi")?;
            let m_lo = field_nat(name, rows, look, v.mrand_lo, "QEprocLook/mRandLo")?;
            let m_rand = ((m_hi as u128) << 64) | m_lo as u128;
            if m_rand > ONE_FP {
                return Err(ctx_err(name, "mRand > 1".into()));
            }
            if m_rand < p.m_det {
                return Err(ctx_err(
                    name,
                    "mRand < mDet (the randomized look can only improve)".into(),
                ));
            }
            // The declared protocol row travels with the claim
            // (content is a declaration, not machine-checkable).
            let proto_row = sole_field(name, rows, look, v.u_protocol, "QEprocLook/uProtocol")?;
            match value_lit(name, proto_row, "QEprocLook/uProtocol")?.view() {
                LiteralView::Str(s) if !s.is_empty() => {}
                LiteralView::Str(_) => {
                    return Err(ctx_err(name, "uProtocol declaration is empty".into()));
                }
                _ => {
                    return Err(ctx_err(name, "uProtocol is not a Str literal".into()));
                }
            }
            let u = field_qq(name, rows, look, v.u, "QEprocLook/u")?;
            // u in (0,1), >= 2^-60, binary64-representable: dyadic
            // denominator with numerator below 2^53 (in lowest terms —
            // the canonical Q form — this characterizes exactly the
            // normal binary64 values of the guarded range).
            if !u.is_nonneg() || u.is_zero() {
                return Err(ctx_err(name, format!("u {u:?} not in (0,1)")));
            }
            let (u_num, u_den) = (u.num().clone(), u.den().clone());
            if u_num.magnitude() >= &u_den {
                return Err(ctx_err(name, "u not below 1".into()));
            }
            // u >= 2^-60  <=>  num·2^60 >= den.
            if (u_num.magnitude() << 60u32) < u_den {
                return Err(ctx_err(name, "u below the 2^-60 guard".into()));
            }
            if u_den.count_ones() != 1 {
                return Err(ctx_err(name, "u denominator is not a power of two".into()));
            }
            if u_num.magnitude().bits() > 53 {
                return Err(ctx_err(
                    name,
                    "u numerator exceeds binary64 significand width".into(),
                ));
            }
            let bound_rand = field_qq(name, rows, look, v.bound_rand, "QEprocLook/boundRand")?;

            let l_rand = wealth_fp(&ys, m_rand);
            // wealth·den(u) >= 2^96·alphaInv·num(u), exactly. After the
            // guards: den <= 2^113 (u >= 2^-60, num < 2^53) and
            // num < 2^53, so both sides fit the 256-bit compare.
            let den_u128 = u128::try_from(&u_den)
                .map_err(|_| ctx_err(name, "u denominator beyond the guarded range".into()))?;
            let num_u128 = u128::try_from(u_num.magnitude()).expect("u numerator below 2^53");
            if mul_cmp(l_rand, den_u128, thr, num_u128) == core::cmp::Ordering::Less {
                return Ok(false);
            }
            Ok(bound_tie(p.k_lo, p.k_hi, m_rand, &bound_rand))
        }
    }
}

// ---------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// `⌊x·2^32⌋` computed exactly from the IEEE-754 bits (the
    /// workshop u4 checker's `floor_x_2p32`, ported for the
    /// equivalence test below).
    fn floor_x_2p32_bits(x: f64) -> i128 {
        assert!(x.is_finite() && x.abs() <= 1e12);
        let bits = x.to_bits();
        let neg = bits >> 63 == 1;
        let biased = ((bits >> 52) & 0x7ff) as i32;
        let frac = bits & ((1u64 << 52) - 1);
        let (mant, e) = if biased == 0 {
            (frac, -1074i32)
        } else {
            (frac | (1u64 << 52), biased - 1075)
        };
        if mant == 0 {
            return 0;
        }
        let shift = e + 32;
        let (q, inexact) = if shift >= 0 {
            ((mant as u128) << (shift as u32), false)
        } else {
            let s = (-shift) as u32;
            if s >= 128 {
                (0, true)
            } else {
                (
                    (mant as u128) >> s,
                    ((mant as u128) & ((1u128 << s) - 1)) != 0,
                )
            }
        };
        if neg {
            -(q as i128) - if inexact { 1 } else { 0 }
        } else {
            q as i128
        }
    }

    /// The exact rational of a finite f64.
    fn f64_to_q(x: f64) -> (BigInt, BigUint) {
        let bits = x.to_bits();
        let neg = bits >> 63 == 1;
        let biased = ((bits >> 52) & 0x7ff) as i32;
        let frac = bits & ((1u64 << 52) - 1);
        let (mant, e) = if biased == 0 {
            (frac, -1074i32)
        } else {
            (frac | (1u64 << 52), biased - 1075)
        };
        let mut num = BigInt::from(mant);
        if neg {
            num = -num;
        }
        if e >= 0 {
            (num << (e as u32), BigUint::one())
        } else {
            (num, BigUint::one() << ((-e) as u32))
        }
    }

    #[test]
    fn grid_is_the_pinned_ladder() {
        // 15/16, 5/8, 15/32, 5/16 … alternating ratios 2/3 and 3/4,
        // down to 5/1024.
        assert_eq!(GRID[0], (15, 4));
        assert_eq!(GRID[1], (5, 3));
        assert_eq!(GRID[15], (5, 10));
        for (j, &(num, shift)) in GRID.iter().enumerate() {
            let expect = if j % 2 == 0 {
                (15u8, 4 + (j as u8) / 2)
            } else {
                (5u8, 3 + (j as u8 - 1) / 2)
            };
            assert_eq!((num, shift), expect, "grid entry {j}");
        }
    }

    proptest! {
        /// Q-path scaling equals the bit-path scaling on random
        /// doubles (the transcription-fidelity theorem, empirically).
        #[test]
        fn floor_q_matches_floor_bits(x in -1.0e12f64..1.0e12f64) {
            let (num, den) = f64_to_q(x);
            prop_assert_eq!(floor_x_2p32_q(&num, &den), floor_x_2p32_bits(x));
        }

        /// The fixed-point wealth never exceeds the exact wealth
        /// (every rounding directed down), so fp-ACCEPT implies
        /// exact-ACCEPT.
        #[test]
        fn wealth_fp_is_a_lower_bound(
            ys in proptest::collection::vec(0u128..=ONE_FP, 1..24),
            m in 0u128..=ONE_FP,
        ) {
            let l = wealth_fp(&ys, m);
            let ys_q: Vec<QQ> = ys
                .iter()
                .map(|y| QQ::new(BigInt::from(*y), BigUint::from(ONE_FP)))
                .collect();
            let m_q = QQ::new(BigInt::from(m), BigUint::from(ONE_FP));
            let exact = wealth_exact(&ys_q, &m_q);
            // l/2^96 <= exact  <=>  l·den(exact) <= num(exact)·2^96,
            // via QQ comparison.
            let l_q = QQ::new(BigInt::from(l), BigUint::from(ONE_FP));
            prop_assert!(l_q.cmp_qq(&exact) != core::cmp::Ordering::Greater);
        }
    }

    #[test]
    fn y_scaling_endpoints() {
        // r = kLo scales to 0; r = kHi scales to ONE; midpoint halves.
        let (lo, hi) = (-3i64, 5i64);
        let y0 = y_fp_from_q(&BigInt::from(-3), &BigUint::one(), lo, hi, false).unwrap();
        assert_eq!(y0, 0);
        let y1 = y_fp_from_q(&BigInt::from(5), &BigUint::one(), lo, hi, false).unwrap();
        assert_eq!(y1, ONE_FP);
        let ymid = y_fp_from_q(&BigInt::from(1), &BigUint::one(), lo, hi, false).unwrap();
        assert_eq!(ymid, ONE_FP / 2);
        // Above kHi caps; below kLo refuses (min-cap) / clamps (clip).
        let ycap = y_fp_from_q(&BigInt::from(9), &BigUint::one(), lo, hi, false).unwrap();
        assert_eq!(ycap, ONE_FP);
        assert!(y_fp_from_q(&BigInt::from(-4), &BigUint::one(), lo, hi, false).is_err());
        let yclamp = y_fp_from_q(&BigInt::from(-4), &BigUint::one(), lo, hi, true).unwrap();
        assert_eq!(yclamp, 0);
    }

    #[test]
    fn wealth_grows_on_a_favorable_ledger() {
        // All-ones ledger at m = 1/2: every factor is 1 + λ/2 > 1, so
        // wealth clears any modest threshold at moderate n.
        let ys = vec![ONE_FP; 64];
        let m = ONE_FP / 2;
        let l = wealth_fp(&ys, m);
        assert!(l > ONE_FP * 100, "wealth {l} should dwarf 100");
        // And at m = 1 the walk cannot grow (y − m = 0 everywhere).
        let flat = wealth_fp(&ys, ONE_FP);
        assert!(flat <= ONE_FP);
    }

    #[test]
    fn bound_tie_exactness() {
        // kLo = -190381, kHi = 340, m = 2^95 (= 1/2): bound =
        // kLo + (kHi−kLo)/2 = -95020.5.
        let m = ONE_FP / 2;
        let claimed = QQ::new(BigInt::from(-190041i64), BigUint::from(2u8));
        assert!(bound_tie(-190381, 340, m, &claimed));
        let off = QQ::new(BigInt::from(-190040i64), BigUint::from(2u8));
        assert!(!bound_tie(-190381, 340, m, &off));
    }
}
