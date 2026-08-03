//! Exact sparse multivariate polynomials over `QQ` — the canonical form
//! of `Term.toPoly` (Lean `Core/QArith.lean` `Poly`), transcribed fresh
//! for the certificate side-condition evaluator families.
//!
//! Representation: `BTreeMap<Mono, QQ>` with nonzero coefficients only,
//! monomials as sorted `(var, exp)` lists with positive exponents. The
//! Lean `Poly` is a canonically SORTED assoc list with the same
//! merge/zero-drop laws; both representations are injective images of
//! the same function (monomial → coefficient), so **canonical-form
//! equality here decides exactly the Lean predicate** — the bridge the
//! `polynomialCanonicalEq` / `farkasCheck` / `syzygyCheck` evaluators
//! stand on. Nothing here rescales (the F7 discipline: canonicalization
//! means sorted + zero-dropped, NEVER primitive-integer rescaling).
//!
//! Variables are `u64` keys: wire indices for the idx-free walks, the
//! Lean `wireCoordKey` pairing for the G1 wire-coordinate branch.

use crate::qq::QQ;
use std::collections::BTreeMap;

/// Sparse monomial: `(var, exp)` pairs, sorted by var, exps > 0.
pub type Mono = Vec<(u64, u32)>;

/// Canonical sparse polynomial: monomial → nonzero coefficient.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct QPoly(pub BTreeMap<Mono, QQ>);

pub(crate) fn mono_mul(a: &Mono, b: &Mono) -> Mono {
    let mut out: Mono = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].0.cmp(&b[j].0) {
            std::cmp::Ordering::Less => {
                out.push(a[i]);
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                out.push(b[j]);
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                out.push((a[i].0, a[i].1 + b[j].1));
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

impl QPoly {
    pub fn zero() -> QPoly {
        QPoly::default()
    }

    pub fn constant(c: QQ) -> QPoly {
        let mut m = BTreeMap::new();
        if !c.is_zero() {
            m.insert(Vec::new(), c);
        }
        QPoly(m)
    }

    pub fn var(v: u64) -> QPoly {
        let mut m = BTreeMap::new();
        m.insert(vec![(v, 1)], QQ::one());
        QPoly(m)
    }

    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    fn add_term(&mut self, m: Mono, c: QQ) {
        use std::collections::btree_map::Entry;
        if c.is_zero() {
            return;
        }
        match self.0.entry(m) {
            Entry::Vacant(e) => {
                e.insert(c);
            }
            Entry::Occupied(mut e) => {
                let s = e.get().add(&c);
                if s.is_zero() {
                    e.remove();
                } else {
                    *e.get_mut() = s;
                }
            }
        }
    }

    pub fn add(&self, o: &QPoly) -> QPoly {
        let mut out = self.clone();
        for (m, c) in &o.0 {
            out.add_term(m.clone(), c.clone());
        }
        out
    }

    pub fn neg(&self) -> QPoly {
        QPoly(self.0.iter().map(|(m, c)| (m.clone(), c.neg())).collect())
    }

    pub fn sub(&self, o: &QPoly) -> QPoly {
        self.add(&o.neg())
    }

    pub fn scale(&self, a: &QQ) -> QPoly {
        if a.is_zero() {
            return QPoly::zero();
        }
        QPoly(self.0.iter().map(|(m, c)| (m.clone(), a.mul(c))).collect())
    }

    pub fn mul(&self, o: &QPoly) -> QPoly {
        let mut out = QPoly::zero();
        for (ma, ca) in &self.0 {
            for (mb, cb) in &o.0 {
                out.add_term(mono_mul(ma, mb), ca.mul(cb));
            }
        }
        out
    }

    /// Exact partial evaluation: substitute variable `v := val`,
    /// eliminating `v` from every monomial (the face-restriction
    /// recompute — restricting to the face `w_v = bound` IS this
    /// substitution). Pure fold over `add_term`, so the result is
    /// canonical (merged, zero-dropped) by construction.
    pub fn substitute_var(&self, v: u64, val: &QQ) -> QPoly {
        let mut out = QPoly::zero();
        for (m, c) in &self.0 {
            match m.iter().position(|(mv, _)| *mv == v) {
                None => out.add_term(m.clone(), c.clone()),
                Some(i) => {
                    let e = m[i].1;
                    let mut pow = QQ::one();
                    for _ in 0..e {
                        pow = pow.mul(val);
                    }
                    let mut rest = m.clone();
                    rest.remove(i);
                    out.add_term(rest, c.mul(&pow));
                }
            }
        }
        out
    }

    /// Ground evaluation at the empty assignment: `Some(c)` iff the
    /// polynomial is constant (the `constExactEvalTrue` seam).
    pub fn as_const(&self) -> Option<QQ> {
        match self.0.len() {
            0 => Some(QQ::zero()),
            1 => {
                let (m, c) = self.0.iter().next().expect("len 1");
                if m.is_empty() {
                    Some(c.clone())
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

/// Lean `wireCoordKey` (Catalogue.lean): the injective (wire, coord) →
/// variable pairing of the G1 wire-aware idx translation. `None` on
/// u64 overflow (unreachable for real certificates — wire and coord
/// indices are u32-born — but a refusal beats a wrap).
pub fn wire_coord_key(w: u64, i: u64) -> Option<u64> {
    if w < i {
        i.checked_mul(i)?.checked_add(w)
    } else {
        w.checked_mul(w)?.checked_add(w)?.checked_add(i)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::{BigInt, BigUint};

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    #[test]
    fn ring_laws_smoke() {
        let x = QPoly::var(0);
        let y = QPoly::var(1);
        // (x + y)(x - y) = x^2 - y^2
        let lhs = x.add(&y).mul(&x.sub(&y));
        let x2 = x.mul(&x);
        let y2 = y.mul(&y);
        assert_eq!(lhs, x2.sub(&y2));
        // x - x = 0 with the entry dropped, not zero-coeffed
        assert!(x.sub(&x).is_zero());
        // scale by 0 kills
        assert!(x.scale(&QQ::zero()).is_zero());
    }

    #[test]
    fn substitute_var_is_partial_eval() {
        // p = x^2 y + 3 x - y/2; x := -2  ⇒  4y - 6 - y/2 = (7/2)y - 6
        let x = QPoly::var(0);
        let y = QPoly::var(1);
        let p = x
            .mul(&x)
            .mul(&y)
            .add(&x.scale(&q(3, 1)))
            .sub(&y.scale(&q(1, 2)));
        let s = p.substitute_var(0, &q(-2, 1));
        let expect = y.scale(&q(7, 2)).sub(&QPoly::constant(q(6, 1)));
        assert_eq!(s, expect);
        // substituting an absent variable is the identity
        assert_eq!(p.substitute_var(9, &q(5, 1)), p);
        // canonicality: cancellation drops entries (x := 0 kills x-terms)
        let zx = p.substitute_var(0, &QQ::zero());
        assert_eq!(zx, y.scale(&q(-1, 2)));
    }

    #[test]
    fn no_rescale_discipline() {
        // 2x + 2 stays 2x + 2 (F7: no primitive-integer rescale).
        let p = QPoly::var(0).scale(&q(2, 1)).add(&QPoly::constant(q(2, 1)));
        assert_eq!(p.0.get(&vec![(0u64, 1u32)] as &Mono), Some(&q(2, 1)));
        assert_eq!(p.0.get(&Vec::new() as &Mono), Some(&q(2, 1)));
    }

    #[test]
    fn coord_key_matches_lean_cases() {
        // Lean: if w < i then i*i + w else w*w + w + i
        assert_eq!(wire_coord_key(0, 0), Some(0));
        assert_eq!(wire_coord_key(1, 0), Some(2)); // 1+1+0
        assert_eq!(wire_coord_key(0, 1), Some(1)); // 1*1+0
        assert_eq!(wire_coord_key(2, 3), Some(11)); // 9+2
        assert_eq!(wire_coord_key(3, 2), Some(14)); // 9+3+2
                                                    // injectivity spot-check over a grid
        let mut seen = std::collections::HashSet::new();
        for w in 0..40u64 {
            for i in 0..40u64 {
                assert!(seen.insert(wire_coord_key(w, i).unwrap()));
            }
        }
    }
}
