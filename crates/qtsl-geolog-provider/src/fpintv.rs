//! Validated floating-point interval substrate for the Bernstein-cone
//! float lane (`allForwardDiffBernIntvEnclosuresSatisfyP`).
//!
//! Semantic authority: `lean/qtsl/Qtsl/Core/Dyadic.lean` — `FloatFmt`
//! with its **exact ℚ→ℚ** rounding maps (`rdnRaw` = grid floor at
//! `gridExp q = max eMin (intLog2 |q| + 1 − prec)`; `rdn` adds the
//! finite clamps; `rup q = −(rdn (−q))`) and the four standard
//! formats; `Core/Prim.lean` `intLog2`/`clog2`. Every function here is
//! a transcription of those definitions over [`crate::qq::QQ`] —
//! softfloat by integers, bit-exact to the Lean, no hardware FP, no
//! rounding-mode control (which would be unsound under the compiler's
//! round-nearest assumptions anyway).
//!
//! **∞-routing (the one soundness trap in the authority):** `rdn`'s
//! bottom clamp (`q < −maxFin ↦ −maxFin`) returns a value ABOVE `q` —
//! a valid finite-format *rounding*, an invalid *enclosure lower
//! endpoint*. Enclosure code therefore uses [`round_down`] /
//! [`round_up`], which follow the `Core/ERat.lean` `roundE` story:
//! below-range rounds down to [`End::NegInf`], above-range rounds up
//! to [`End::PosInf`], and the finite arms delegate to `rdn`/`rup`
//! (whose remaining clamps are then directed correctly: `maxFin ≤ q ↦
//! maxFin ≤ q` ✓). An ∞ endpoint never witnesses anything downstream;
//! it records that the computation left the finite range.
//!
//! **Interval semantics adjudication**: endpoint products follow
//! CONTAINMENT semantics over the reals — the enclosed true values
//! are finite rationals, so `0·∞ = 0` (the product set
//! `{x·y : x ∈ [0,0], y ∈ [c,∞)}` is `{0}`), where `ERat.mul?` is
//! deliberately partial. The two answer different questions (set
//! image vs. scalar extension); IEEE-1788 makes the same call.
//!
//! Working precision stays bounded by construction: every STORED
//! endpoint is on the format grid (mantissa below `2^prec`, exponent
//! clamped), so transient op inputs are grid dyadics and the exact
//! rational op before rounding costs ~2·prec bits — the honest
//! reading of the frozen spec's "No exact ℚ arithmetic at check
//! time", which bans R15's unbounded-precision pipeline, not integers
//! implementing float semantics.

use crate::qq::QQ;
use crate::theory::{Chid, DomainSig, SortKey, TheoryIndex};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use std::cmp::Ordering;

// ---------------------------------------------------------------------
// Formats (Lean `FloatFmt` + the four standard instances)
// ---------------------------------------------------------------------

/// A float format as mantissa/exponent bounds (Lean `FloatFmt`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FpFmt {
    /// Mantissa precision in bits (Lean `prec`, `0 < prec`).
    pub prec: u32,
    /// Minimum grid exponent (Lean `eMin`).
    pub e_min: i64,
    /// Maximum grid exponent (Lean `eMax`).
    pub e_max: i64,
}

/// Lean `FloatFmt.f16` : ⟨11, −24, 5⟩.
pub const F16: FpFmt = FpFmt {
    prec: 11,
    e_min: -24,
    e_max: 5,
};
/// Lean `FloatFmt.bf16` : ⟨8, −133, 120⟩.
pub const BF16: FpFmt = FpFmt {
    prec: 8,
    e_min: -133,
    e_max: 120,
};
/// Lean `FloatFmt.f32` : ⟨24, −149, 104⟩.
pub const F32: FpFmt = FpFmt {
    prec: 24,
    e_min: -149,
    e_max: 104,
};
/// Lean `FloatFmt.f64` : ⟨53, −1074, 971⟩.
pub const F64: FpFmt = FpFmt {
    prec: 53,
    e_min: -1074,
    e_max: 971,
};

/// `2^g` as an exact rational (`g` of either sign).
fn pow2(g: i64) -> QQ {
    if g >= 0 {
        QQ::new(BigInt::one() << (g as u64), BigUint::one())
    } else {
        QQ::new(BigInt::one(), BigUint::one() << ((-g) as u64))
    }
}

/// Floor division `a / b` with `b ≥ 1`, rounding toward −∞ (BigInt `/`
/// truncates toward zero; adjust when a remainder survives on a
/// negative dividend).
fn floor_div(a: &BigInt, b: &BigUint) -> BigInt {
    let b = BigInt::from(b.clone());
    let q = a / &b;
    let r = a - &q * &b;
    if r.is_zero() || a.sign() != num_bigint::Sign::Minus {
        q
    } else {
        q - BigInt::one()
    }
}

/// `⌊q⌋` (toward −∞).
fn qq_floor(q: &QQ) -> BigInt {
    floor_div(q.num(), q.den())
}

/// `⌈q⌉` = `−⌊−q⌋`.
fn qq_ceil(q: &QQ) -> BigInt {
    -floor_div(&(-q.num()), q.den())
}

/// Lean `Nat.log2` (`log2 n = if 2 ≤ n then log2 (n/2) + 1 else 0`):
/// `⌊log₂ n⌋` for `n ≥ 1`, and `0` at `n = 0`.
fn nat_log2(n: &BigUint) -> i64 {
    if n.is_zero() {
        0
    } else {
        (n.bits() - 1) as i64
    }
}

/// Lean `Prim.clog2` (`clog2 n = if 2 ≤ n then clog2 ((n+1)/2) + 1
/// else 0`) — transcribed as the same recursion, iteratively.
fn clog2(n: &BigUint) -> i64 {
    let two = BigUint::from(2u32);
    let mut n = n.clone();
    let mut c = 0i64;
    while n >= two {
        n = (&n + BigUint::one()) >> 1;
        c += 1;
    }
    c
}

/// Lean `Prim.intLog2`:
/// `if 1 ≤ q then Nat.log2 q.floor.toNat else −(clog2 q⁻¹.ceil.toNat)`.
/// (Lean `Rat` inverts 0 to 0 and `toNat` clamps negatives to 0 —
/// both arms transcribed; callers pass `|q|`.)
pub fn int_log2(q: &QQ) -> i64 {
    if q.cmp_qq(&QQ::one()) != Ordering::Less {
        // q ≥ 1: floor is a nonnegative integer.
        let f = qq_floor(q);
        nat_log2(f.magnitude())
    } else if q.is_zero() || !q.is_nonneg() {
        // q⁻¹ ≤ 0 (or 0⁻¹ = 0): ceil.toNat = 0, clog2 0 = 0.
        0
    } else {
        // 0 < q < 1: −clog2(⌈1/q⌉).
        let inv = QQ::new(BigInt::from(q.den().clone()), q.num().magnitude().clone());
        let c = qq_ceil(&inv);
        -clog2(c.magnitude())
    }
}

impl FpFmt {
    /// Lean `FloatFmt.maxFin` = `(2^prec − 1)·2^eMax`.
    pub fn max_fin(&self) -> QQ {
        let m = (BigInt::one() << (self.prec as u64)) - BigInt::one();
        QQ::new(m, BigUint::one()).mul(&pow2(self.e_max))
    }

    /// Lean `FloatFmt.gridExp` = `max eMin (intLog2 |q| + 1 − prec)`.
    pub fn grid_exp(&self, q: &QQ) -> i64 {
        self.e_min.max(int_log2(&q.abs()) + 1 - self.prec as i64)
    }

    /// Lean `FloatFmt.rdnRaw` = `⌊q / 2^gridExp⌋ · 2^gridExp`.
    fn rdn_raw(&self, q: &QQ) -> QQ {
        let g = self.grid_exp(q);
        let scaled = q.mul(&pow2(-g));
        QQ::new(qq_floor(&scaled), BigUint::one()).mul(&pow2(g))
    }

    /// Lean `FloatFmt.rdn` (finite-format round-down, WITH the clamps
    /// — the bottom clamp is a saturation, not a lower bound; use
    /// [`round_down`] for enclosure endpoints).
    pub fn rdn(&self, q: &QQ) -> QQ {
        let mf = self.max_fin();
        if mf.cmp_qq(q) != Ordering::Greater {
            mf
        } else if q.cmp_qq(&mf.neg()) == Ordering::Less {
            mf.neg()
        } else {
            self.rdn_raw(q)
        }
    }

    /// Lean `FloatFmt.rup q = −(rdn (−q))`.
    pub fn rup(&self, q: &QQ) -> QQ {
        self.rdn(&q.neg()).neg()
    }
}

// ---------------------------------------------------------------------
// Extended endpoints + intervals
// ---------------------------------------------------------------------

/// An interval endpoint in the extended line (`Core/ERat.lean` kin).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum End {
    NegInf,
    Fin(QQ),
    PosInf,
}

impl End {
    fn cmp_end(&self, o: &End) -> Ordering {
        use End::*;
        match (self, o) {
            (NegInf, NegInf) | (PosInf, PosInf) => Ordering::Equal,
            (NegInf, _) | (_, PosInf) => Ordering::Less,
            (_, NegInf) | (PosInf, _) => Ordering::Greater,
            (Fin(a), Fin(b)) => a.cmp_qq(b),
        }
    }

    fn neg(&self) -> End {
        match self {
            End::NegInf => End::PosInf,
            End::PosInf => End::NegInf,
            End::Fin(q) => End::Fin(q.neg()),
        }
    }
}

/// `roundE`-style directed rounding to a VALID lower bound: below the
/// finite range routes to −∞ (never the finite clamp); in range,
/// `rdn q ≤ q` holds (`maxFin ≤ q ↦ maxFin` included).
pub fn round_down(fmt: &FpFmt, q: &QQ) -> End {
    if q.cmp_qq(&fmt.max_fin().neg()) == Ordering::Less {
        End::NegInf
    } else {
        End::Fin(fmt.rdn(q))
    }
}

/// Dual: above the finite range routes to +∞; in range `q ≤ rup q`.
pub fn round_up(fmt: &FpFmt, q: &QQ) -> End {
    if fmt.max_fin().cmp_qq(q) == Ordering::Less {
        End::PosInf
    } else {
        End::Fin(fmt.rup(q))
    }
}

/// A validated interval: `lo ∈ {−∞, Fin}`, `hi ∈ {Fin, +∞}`,
/// `lo ≤ hi`; finite endpoints are on the format grid after every op.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FpIv {
    pub lo: End,
    pub hi: End,
}

impl FpIv {
    /// Enclose an exact rational.
    pub fn from_q(fmt: &FpFmt, q: &QQ) -> FpIv {
        FpIv {
            lo: round_down(fmt, q),
            hi: round_up(fmt, q),
        }
    }

    /// The exact zero point (representable at every format).
    pub fn zero() -> FpIv {
        FpIv {
            lo: End::Fin(QQ::zero()),
            hi: End::Fin(QQ::zero()),
        }
    }

    /// The exact one point (representable at every format: `prec ≥ 1`,
    /// `eMin ≤ 0`).
    pub fn one() -> FpIv {
        FpIv {
            lo: End::Fin(QQ::one()),
            hi: End::Fin(QQ::one()),
        }
    }

    pub fn is_exact_zero(&self) -> bool {
        matches!((&self.lo, &self.hi), (End::Fin(a), End::Fin(b)) if a.is_zero() && b.is_zero())
    }

    pub fn neg(&self) -> FpIv {
        FpIv {
            lo: self.hi.neg(),
            hi: self.lo.neg(),
        }
    }

    pub fn add(&self, fmt: &FpFmt, o: &FpIv) -> FpIv {
        let lo = match (&self.lo, &o.lo) {
            (End::Fin(a), End::Fin(b)) => round_down(fmt, &a.add(b)),
            _ => End::NegInf,
        };
        let hi = match (&self.hi, &o.hi) {
            (End::Fin(a), End::Fin(b)) => round_up(fmt, &a.add(b)),
            _ => End::PosInf,
        };
        FpIv { lo, hi }
    }

    /// Endpoint product under containment semantics (`0·∞ = 0` — the
    /// module-header adjudication). Exact where finite; rounding is
    /// applied by the caller to the selected extremes.
    fn ext_mul(a: &End, b: &End) -> End {
        use End::*;
        match (a, b) {
            (Fin(x), Fin(y)) => Fin(x.mul(y)),
            (Fin(x), inf) | (inf, Fin(x)) => {
                if x.is_zero() {
                    Fin(QQ::zero())
                } else if x.is_nonneg() {
                    inf.clone()
                } else {
                    inf.neg()
                }
            }
            (PosInf, PosInf) | (NegInf, NegInf) => PosInf,
            _ => NegInf,
        }
    }

    pub fn mul(&self, fmt: &FpFmt, o: &FpIv) -> FpIv {
        let combos = [
            Self::ext_mul(&self.lo, &o.lo),
            Self::ext_mul(&self.lo, &o.hi),
            Self::ext_mul(&self.hi, &o.lo),
            Self::ext_mul(&self.hi, &o.hi),
        ];
        let mut lo_raw = combos[0].clone();
        let mut hi_raw = combos[0].clone();
        for c in &combos[1..] {
            if c.cmp_end(&lo_raw) == Ordering::Less {
                lo_raw = c.clone();
            }
            if c.cmp_end(&hi_raw) == Ordering::Greater {
                hi_raw = c.clone();
            }
        }
        let lo = match lo_raw {
            End::Fin(q) => round_down(fmt, &q),
            e => e,
        };
        let hi = match hi_raw {
            End::Fin(q) => round_up(fmt, &q),
            e => e,
        };
        FpIv { lo, hi }
    }

    /// Scale by an exact rational (a point factor; the factor itself
    /// need not be representable — outward rounding lands the result
    /// on the grid).
    pub fn scale(&self, fmt: &FpFmt, c: &QQ) -> FpIv {
        let point = FpIv {
            lo: End::Fin(c.clone()),
            hi: End::Fin(c.clone()),
        };
        self.mul(fmt, &point)
    }

    /// Divide by an exact positive integer (multinomial denominators).
    pub fn div_nat(&self, fmt: &FpFmt, n: &BigUint) -> FpIv {
        debug_assert!(!n.is_zero(), "positive divisor");
        let d = QQ::new(BigInt::one(), n.clone());
        self.scale(fmt, &d)
    }
}

// ---------------------------------------------------------------------
// Dtype vocabulary + row decode
// ---------------------------------------------------------------------

/// The float kinds this lane binds (design note §5: non-float kinds
/// refuse — the float lane's honest boundary).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FloatKind {
    F16,
    Bf16,
    F32,
    F64,
}

impl FloatKind {
    pub fn fmt(&self) -> &'static FpFmt {
        match self {
            FloatKind::F16 => &F16,
            FloatKind::Bf16 => &BF16,
            FloatKind::F32 => &F32,
            FloatKind::F64 => &F64,
        }
    }
}

/// The Dtype theory's resolved vocabulary: axis fields, the
/// constructor, and every nullary constant the decode dispatches on —
/// name-selected once at construction and shape-verified, exactly as
/// the sibling vocab groups.
#[derive(Debug, Clone)]
pub struct DtypeVocab {
    /// `Dtype/kind : Dtype -> Kind`.
    pub(crate) kind_field: Chid,
    /// `Dtype/sign : Dtype -> Sign`.
    pub(crate) sign_field: Chid,
    /// `Dtype/ext : Dtype -> Ext`.
    pub(crate) ext_field: Chid,
    /// `mkDtype : [k: Kind, s: Sign, e: Ext] -> Dtype`.
    pub(crate) mk_dtype: Chid,
    /// Kind constants, float lane: KF16, KF16bf, KF32, KF64.
    pub(crate) k_f16: Chid,
    pub(crate) k_f16bf: Chid,
    pub(crate) k_f32: Chid,
    pub(crate) k_f64: Chid,
    /// Kind constants, exact lane (recognized to refuse by name).
    pub(crate) k_bool: Chid,
    pub(crate) k_int: Chid,
    pub(crate) k_rat: Chid,
    /// Sign constants.
    pub(crate) s_nn: Chid,
    pub(crate) s_s: Chid,
    /// Ext constants.
    pub(crate) e_fin: Chid,
    pub(crate) e_ext: Chid,
    /// Dtype alias constants (`F64` binds the float lane directly;
    /// `Q`/`Z`/`Nat`/`B` are recognized to refuse by name).
    pub(crate) alias_f64: Chid,
    pub(crate) alias_q: Chid,
    pub(crate) alias_z: Chid,
    pub(crate) alias_nat: Chid,
    pub(crate) alias_b: Chid,
}

/// Build the Dtype vocabulary over the declared indices. `Err` → the
/// float-lane entry is not claimed (declared-but-unbound, safe-fail);
/// the exact sweep's claim is unaffected.
pub fn build_dtype_vocab(
    indices: &[&TheoryIndex],
    dtype_sort: Chid,
    kind_sort: Chid,
    sign_sort: Chid,
    ext_sort: Chid,
) -> Result<DtypeVocab, String> {
    let field = |name: &str, cod: Chid| -> Result<Chid, String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational
                || d.codomain != Some(SortKey::Elem(cod))
                || d.domain != DomainSig::Unary(SortKey::Elem(dtype_sort))
            {
                return Err(format!(
                    "`{name}` does not have the expected field shape \
                     (unary fun on the Dtype sort)"
                ));
            }
            return Ok(d.chid);
        }
        Err(format!("no `{name}` declaration among the swept revisions"))
    };
    let nullary = |name: &str, cod: Chid| -> Result<Chid, String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational
                || d.codomain != Some(SortKey::Elem(cod))
                || d.domain != DomainSig::Nullary
            {
                return Err(format!(
                    "`{name}` does not have the expected nullary-constant shape"
                ));
            }
            return Ok(d.chid);
        }
        Err(format!("no `{name}` declaration among the swept revisions"))
    };
    let mk = |name: &str| -> Result<Chid, String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            let shape_ok = !d.relational
                && d.codomain == Some(SortKey::Elem(dtype_sort))
                && match &d.domain {
                    DomainSig::Record(fields) => matches!(
                        fields.as_slice(),
                        [(f0, SortKey::Elem(s0)), (f1, SortKey::Elem(s1)), (f2, SortKey::Elem(s2))]
                            if f0 == "k" && f1 == "s" && f2 == "e"
                                && *s0 == kind_sort && *s1 == sign_sort && *s2 == ext_sort
                    ),
                    _ => false,
                };
            if !shape_ok {
                return Err(format!(
                    "`{name}` does not have the expected constructor shape \
                     ([k: Kind, s: Sign, e: Ext] -> Dtype)"
                ));
            }
            return Ok(d.chid);
        }
        Err(format!("no `{name}` declaration among the swept revisions"))
    };
    Ok(DtypeVocab {
        kind_field: field("Dtype/kind", kind_sort)?,
        sign_field: field("Dtype/sign", sign_sort)?,
        ext_field: field("Dtype/ext", ext_sort)?,
        mk_dtype: mk("mkDtype")?,
        k_f16: nullary("KF16", kind_sort)?,
        k_f16bf: nullary("KF16bf", kind_sort)?,
        k_f32: nullary("KF32", kind_sort)?,
        k_f64: nullary("KF64", kind_sort)?,
        k_bool: nullary("KBool", kind_sort)?,
        k_int: nullary("KInt", kind_sort)?,
        k_rat: nullary("KRat", kind_sort)?,
        s_nn: nullary("Snn", sign_sort)?,
        s_s: nullary("Ss", sign_sort)?,
        e_fin: nullary("Efin", ext_sort)?,
        e_ext: nullary("Eext", ext_sort)?,
        alias_f64: nullary("F64", dtype_sort)?,
        alias_q: nullary("Q", dtype_sort)?,
        alias_z: nullary("Z", dtype_sort)?,
        alias_nat: nullary("Nat", dtype_sort)?,
        alias_b: nullary("B", dtype_sort)?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    fn qp2(n: i64, g: i64) -> QQ {
        q(n, 1).mul(&pow2(g))
    }

    /// Format parameters against their independently-known values
    /// (f16 max 65504; bf16 max 255·2^120 = 0x7F7F; f32/f64 maxima).
    #[test]
    fn format_maxima() {
        assert_eq!(F16.max_fin(), q(65504, 1));
        assert_eq!(BF16.max_fin(), qp2(255, 120));
        assert_eq!(F32.max_fin(), qp2((1 << 24) - 1, 104));
        let m = (BigInt::one() << 53u32) - BigInt::one();
        assert_eq!(F64.max_fin(), QQ::new(m, BigUint::one()).mul(&pow2(971)));
    }

    /// `intLog2` on both Lean arms (q ≥ 1 via Nat.log2∘floor; q < 1
    /// via −clog2∘ceil∘inv), boundary values included.
    #[test]
    fn int_log2_arms() {
        assert_eq!(int_log2(&q(1, 1)), 0);
        assert_eq!(int_log2(&q(3, 2)), 0);
        assert_eq!(int_log2(&q(2, 1)), 1);
        assert_eq!(int_log2(&q(1, 2)), -1);
        assert_eq!(int_log2(&q(3, 4)), -1);
        assert_eq!(int_log2(&q(1, 4)), -2);
        assert_eq!(int_log2(&q(1, 3)), -2);
        assert_eq!(int_log2(&q(1, 10)), -4);
        assert_eq!(int_log2(&QQ::zero()), 0);
    }

    /// The classic 0.1 witness: `rdn(1/10)` at f64 is one ulp below
    /// the round-nearest value 7205759403792794·2⁻⁵⁶.
    #[test]
    fn f64_tenth() {
        let got = F64.rdn(&q(1, 10));
        assert_eq!(got, qp2(7205759403792793, -56));
        let up = F64.rup(&q(1, 10));
        assert_eq!(up, qp2(7205759403792794, -56));
        // Directedness around the true value.
        assert!(got.cmp_qq(&q(1, 10)) == Ordering::Less);
        assert!(up.cmp_qq(&q(1, 10)) == Ordering::Greater);
    }

    /// Subnormal grid: below half the smallest subnormal rounds down
    /// to zero and up to 2⁻¹⁰⁷⁴ (the f64 grid floor at eMin).
    #[test]
    fn f64_subnormal_grid() {
        let tiny = pow2(-1080);
        assert_eq!(F64.rdn(&tiny), QQ::zero());
        assert_eq!(F64.rup(&tiny), pow2(-1074));
        // Representable values are fixed points, both directions.
        let sub = pow2(-1074);
        assert_eq!(F64.rdn(&sub), sub);
        assert_eq!(F64.rup(&sub), sub);
    }

    /// The ∞-routing arms: the finite clamp is a saturation, never an
    /// enclosure endpoint.
    #[test]
    fn round_infinity_arms() {
        let big = pow2(1030);
        assert_eq!(round_down(&F64, &big.neg()), End::NegInf);
        assert_eq!(round_up(&F64, &big), End::PosInf);
        // The directed-valid finite arms survive: an above-range value
        // rounds DOWN to maxFin (≤ q ✓) and a below-range value rounds
        // UP to −maxFin (≥ q ✓).
        assert_eq!(round_down(&F64, &big), End::Fin(F64.max_fin()));
        assert_eq!(round_up(&F64, &big.neg()), End::Fin(F64.max_fin().neg()));
    }

    /// Representable fixed points at coarser formats + directedness
    /// on a non-representable value.
    #[test]
    fn f16_grid() {
        // 1/10 at f16: grid exp = max(−24, −4 + 1 − 11) = −14;
        // ⌊2¹⁴/10⌋ = 1638 → rdn = 1638·2⁻¹⁴, rup = 1639·2⁻¹⁴.
        assert_eq!(F16.rdn(&q(1, 10)), qp2(1638, -14));
        assert_eq!(F16.rup(&q(1, 10)), qp2(1639, -14));
        assert_eq!(F16.rdn(&q(3, 4)), q(3, 4));
        assert_eq!(F16.rup(&q(3, 4)), q(3, 4));
    }

    /// Interval ops: containment + outward rounding + the 0·∞ rule.
    #[test]
    fn interval_ops() {
        let a = FpIv::from_q(&F64, &q(1, 10));
        let b = FpIv::from_q(&F64, &q(1, 3));
        let s = a.add(&F64, &b);
        let (End::Fin(lo), End::Fin(hi)) = (&s.lo, &s.hi) else {
            panic!("finite");
        };
        let exact = q(1, 10).add(&q(1, 3));
        assert!(lo.cmp_qq(&exact) == Ordering::Less);
        assert!(hi.cmp_qq(&exact) == Ordering::Greater);

        let p = a.mul(&F64, &b);
        let (End::Fin(plo), End::Fin(phi)) = (&p.lo, &p.hi) else {
            panic!("finite");
        };
        let pex = q(1, 10).mul(&q(1, 3));
        assert!(plo.cmp_qq(&pex) == Ordering::Less);
        assert!(phi.cmp_qq(&pex) == Ordering::Greater);

        // Sign flip under mul by a negative point.
        let n = a.scale(&F64, &q(-1, 1));
        assert_eq!(n, a.neg());

        // 0·[3, +∞) = [0, 0] (containment semantics).
        let unb = FpIv {
            lo: End::Fin(q(3, 1)),
            hi: End::PosInf,
        };
        let z = FpIv::zero().mul(&F64, &unb);
        assert!(z.is_exact_zero());
        // [1,2]·[3, +∞) = [3, +∞).
        let onetwo = FpIv {
            lo: End::Fin(q(1, 1)),
            hi: End::Fin(q(2, 1)),
        };
        let r = onetwo.mul(&F64, &unb);
        assert_eq!(r.lo, End::Fin(q(3, 1)));
        assert_eq!(r.hi, End::PosInf);

        // Division by an exact positive integer.
        let d = FpIv::one().div_nat(&F64, &BigUint::from(3u32));
        let (End::Fin(dlo), End::Fin(dhi)) = (&d.lo, &d.hi) else {
            panic!("finite");
        };
        let third = q(1, 3);
        assert!(dlo.cmp_qq(&third) == Ordering::Less);
        assert!(dhi.cmp_qq(&third) == Ordering::Greater);
    }

    /// Exact dyadics on the grid pass through both endpoints
    /// untouched (zero-width intervals stay zero-width under +/·).
    #[test]
    fn exact_dyadics_zero_width() {
        let half = FpIv::from_q(&F64, &q(1, 2));
        assert_eq!(half.lo, End::Fin(q(1, 2)));
        assert_eq!(half.hi, End::Fin(q(1, 2)));
        let sum = half.add(&F64, &half);
        assert_eq!(sum.lo, End::Fin(q(1, 1)));
        assert_eq!(sum.hi, End::Fin(q(1, 1)));
        let prod = half.mul(&F64, &half);
        assert_eq!(prod.lo, End::Fin(q(1, 4)));
        assert_eq!(prod.hi, End::Fin(q(1, 4)));
    }
}
