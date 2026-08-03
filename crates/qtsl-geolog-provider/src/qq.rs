//! Canonical arbitrary-precision rationals for the certificate
//! side-condition evaluator families — `den >= 1`, `gcd(|num|, den) = 1`, zero canonically `0/1`.
//!
//! Deliberately hand-rolled on the workspace's existing `num-bigint`
//! (no `num-rational` dependency): the three-way differential wants this
//! arm DECORRELATED from an off-the-shelf `BigRational` arm, and the whole
//! surface the families need is add/sub/mul/neg/scale/cmp/abs — small
//! enough that a fresh transcription is cheaper than a dependency and
//! carries independent-error value (decorrelated
//! errors are the differential's power).
//!
//! Payload seam: [`QQ::from_q_literal`] reads the primordial `Q` cell
//! (canonical minimal-LE limbs, signed num / unsigned den — the same
//! view `cmp_q` dispatches on), trusting canonicality exactly as far as
//! the envelope validator enforces it and re-reducing anyway (defence in
//! depth: a non-canonical payload smuggled past validation still yields
//! a CORRECT rational here, never a wrong verdict — reduction is cheap
//! at evaluator scale).

use geolog_envelope::cell::LiteralView;
use geolog_envelope::Literal;
use num_bigint::{BigInt, BigUint, Sign};
use std::cmp::Ordering;

/// Canonical rational: `num/den`, `den >= 1`, reduced, `0 = 0/1`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QQ {
    num: BigInt,
    den: BigUint,
}

fn gcd(mut a: BigUint, mut b: BigUint) -> BigUint {
    use num_traits::Zero;
    while !b.is_zero() {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

impl QQ {
    pub fn zero() -> QQ {
        QQ {
            num: BigInt::from(0),
            den: BigUint::from(1u32),
        }
    }

    pub fn one() -> QQ {
        QQ {
            num: BigInt::from(1),
            den: BigUint::from(1u32),
        }
    }

    pub fn from_int(n: i64) -> QQ {
        QQ {
            num: BigInt::from(n),
            den: BigUint::from(1u32),
        }
    }

    /// Construct + canonicalize. `den = 0` is a caller bug (the payload
    /// seam rejects it before this): loud panic, never a wrong value.
    pub fn new(num: BigInt, den: BigUint) -> QQ {
        use num_traits::Zero;
        assert!(!den.is_zero(), "QQ::new: zero denominator");
        if num.is_zero() {
            return QQ::zero();
        }
        let g = gcd(num.magnitude().clone(), den.clone());
        QQ {
            num: &num / BigInt::from(g.clone()),
            den: &den / &g,
        }
    }

    /// The primordial `Q` literal cell → QQ. `None` on a non-Q literal
    /// or an (impossible-by-validation) zero denominator — the caller
    /// turns that into its own refusal, never a guess.
    pub fn from_q_literal(l: &Literal) -> Option<QQ> {
        let LiteralView::Q { num, den } = l.view() else {
            return None;
        };
        use num_traits::Zero;
        let den = BigUint::from_bytes_le(den);
        if den.is_zero() {
            return None;
        }
        Some(QQ::new(BigInt::from_signed_bytes_le(num), den))
    }

    pub fn is_zero(&self) -> bool {
        use num_traits::Zero;
        self.num.is_zero()
    }

    pub fn is_nonneg(&self) -> bool {
        self.num.sign() != Sign::Minus
    }

    pub fn neg(&self) -> QQ {
        QQ {
            num: -&self.num,
            den: self.den.clone(),
        }
    }

    pub fn abs(&self) -> QQ {
        QQ {
            num: BigInt::from(self.num.magnitude().clone()),
            den: self.den.clone(),
        }
    }

    pub fn add(&self, o: &QQ) -> QQ {
        let num = &self.num * BigInt::from(o.den.clone()) + &o.num * BigInt::from(self.den.clone());
        QQ::new(num, &self.den * &o.den)
    }

    pub fn sub(&self, o: &QQ) -> QQ {
        self.add(&o.neg())
    }

    pub fn mul(&self, o: &QQ) -> QQ {
        QQ::new(&self.num * &o.num, &self.den * &o.den)
    }

    /// Exact comparison by cross-multiplication (dens >= 1 keep signs).
    /// (num bits, den bits): magnitude bit lengths, sign excluded — the
    /// limb-capacity receipt for the batch lane (KCAP tiering).
    pub fn bit_widths(&self) -> (u64, u64) {
        (self.num.magnitude().bits(), self.den.bits())
    }

    pub fn cmp_qq(&self, o: &QQ) -> Ordering {
        let l = &self.num * BigInt::from(o.den.clone());
        let r = &o.num * BigInt::from(self.den.clone());
        l.cmp(&r)
    }

    /// Numerator view (canonical: sign lives here).
    pub fn num(&self) -> &BigInt {
        &self.num
    }

    /// Denominator view (canonical: `>= 1`, coprime to `num`).
    pub fn den(&self) -> &BigUint {
        &self.den
    }

    /// Small-plane packing for the batch-CSR lane: `(num, den)`
    /// where both magnitudes fit machine words. `None` is a capacity
    /// refusal, never a rounding — the caller routes the attempt to the
    /// exact path (DATERWI: defer arithmetic to exact rationals when
    /// inconclusive).
    pub fn to_small(&self) -> Option<(i64, u64)> {
        let num = i64::try_from(&self.num).ok()?;
        let den = u64::try_from(&self.den).ok()?;
        Some((num, den))
    }
}

/// Exact comparison of two canonical `Q` literal cells by signed
/// cross-multiplication (no reduction needed: `den >= 1` on both
/// sides).
pub fn cmp_q(l: &Literal, r: &Literal) -> Ordering {
    let (LiteralView::Q { num: ln, den: ld }, LiteralView::Q { num: rn, den: rd }) =
        (l.view(), r.view())
    else {
        unreachable!("cmp_q callers check Q dtype")
    };
    let left = BigInt::from_signed_bytes_le(ln) * BigInt::from(BigUint::from_bytes_le(rd));
    let right = BigInt::from_signed_bytes_le(rn) * BigInt::from(BigUint::from_bytes_le(ld));
    left.cmp(&right)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    #[test]
    fn canonical_forms() {
        assert_eq!(q(2, 4), q(1, 2));
        assert_eq!(q(-6, 4), q(-3, 2));
        assert_eq!(q(0, 7), QQ::zero());
        assert_eq!(q(5, 1).sub(&q(5, 1)), QQ::zero());
    }

    #[test]
    fn arithmetic() {
        assert_eq!(q(1, 2).add(&q(1, 3)), q(5, 6));
        assert_eq!(q(1, 2).mul(&q(2, 3)), q(1, 3));
        assert_eq!(q(-1, 2).abs(), q(1, 2));
        assert_eq!(q(1, 2).cmp_qq(&q(2, 3)), Ordering::Less);
        assert_eq!(q(-1, 2).cmp_qq(&q(-2, 3)), Ordering::Greater);
        assert!(q(0, 1).is_nonneg() && q(3, 7).is_nonneg() && !q(-3, 7).is_nonneg());
    }

    #[test]
    fn literal_roundtrip() {
        let lit = Literal::q(-22, 8).expect("canonical");
        let v = QQ::from_q_literal(&lit).expect("Q view");
        assert_eq!(v, q(-11, 4));
    }
}
