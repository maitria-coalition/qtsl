//! Barycentric-coordinate substrate: exact-rational decode of simplex
//! geometry rows (`SimpC` vertex tables, `Simplex`/`ExtensionSet`
//! membership) and the affine barycentric-coordinate functions
//! λ_i determined by a simplex — the shared floor under the
//! conclusion-form family ([`crate::blconclform`]) and the forthcoming
//! Bernstein-cone recomputations.
//!
//! Semantic authority: the Lean catalogue's `baryCoeffs1D` /
//! `primAffine` (`lean/qtsl/Qtsl/Core/Catalogue.lean`). The realized
//! construction is one-dimensional: a simplex of exactly two vertices
//! in an ambient line (`ambDim = 1`), whose barycentric coordinates
//! are the two affine functions
//!
//! ```text
//!   λ_a(x) = (V₁ − x) / (V₁ − V₀)      λ_b(x) = (x − V₀) / (V₁ − V₀)
//! ```
//!
//! for vertex coordinates `V₀ = coord(a, 0)`, `V₁ = coord(b, 0)`,
//! vertices in increasing index order (the model filters `Fin.finRange`,
//! which enumerates ascending). Every other shape — ambient dimension
//! other than one, a vertex count other than two — is an explicit
//! `none` branch of the construction, i.e. a DECIDED mismatch for its
//! consumers, not a refusal.
//!
//! One branch deserves its note: the construction also returns `none`
//! when the two vertex coordinates coincide. For a genuine complex
//! that branch is unreachable (the model's `distinctVerts` invariant
//! forces distinct coordinates in some axis, and in one dimension
//! there is only one axis); rows claiming coincident coordinates are
//! mirrored to the same decided `none` the spec function evaluates to,
//! keeping this substrate a literal transcription of its authority.
//!
//! Row-decode discipline (the crate's, as in [`crate::blmask`]): the
//! membership masks and the vertex-coordinate table are the sealed
//! finite data of their subject rows; a membership or coordinate row
//! citing an index at or past its declared bound corresponds to no
//! model state at all (the model is `Fin`-indexed) and REFUSES, as do
//! malformed rows, conflicting duplicates, external references, and
//! missing fields. A decided mismatch is `Ok(false)` territory for the
//! consumer; refusal is never a guessed verdict.

use crate::error::EvalError;
use crate::qq::QQ;
use crate::rowctx::CertRows;
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use num_bigint::{BigInt, BigUint, Sign};
use std::collections::{BTreeMap, BTreeSet};

/// The barycentric substrate's resolved vocabulary: the field funs and
/// membership relations of the simplex-geometry sorts, name-selected
/// once at construction and shape-verified (names select, shapes
/// verify, identities pin).
#[derive(Debug, Clone)]
pub struct BaryVocab {
    /// `Simplex/complex : Simplex -> SimpC`.
    pub(crate) simplex_complex: Chid,
    /// `Simplex/contains : [s: Simplex, v: Nat]` (relational).
    pub(crate) simplex_contains: Chid,
    /// `SimpC/n_vertices : SimpC -> Nat`.
    pub(crate) simpc_n_vertices: Chid,
    /// `SimpC/amb_dim : SimpC -> Nat`.
    pub(crate) simpc_amb_dim: Chid,
    /// `SimpC/coord : [complex: SimpC, j: Nat, v: Nat] -> Q` (field
    /// order bytewise: `complex`, `j`, `v`).
    pub(crate) simpc_coord: Chid,
    /// `ExtensionSet/simplex : ExtensionSet -> Simplex`.
    pub(crate) ext_simplex: Chid,
    /// `ExtensionSet/contains : [S: ExtensionSet, v: Nat]` (relational).
    pub(crate) ext_contains: Chid,
}

/// Build the barycentric vocabulary over the declared indices. `Err` →
/// the dependent families are not claimed (declared-but-unbound,
/// safe-fail).
pub fn build_bary_vocab(
    indices: &[&TheoryIndex],
    simplex_sort: Chid,
    ext_sort: Chid,
    simpc_sort: Chid,
) -> Result<BaryVocab, String> {
    let field = |name: &str, arg: Chid, cod: SortKey| -> Result<Chid, String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational
                || d.codomain != Some(cod)
                || d.domain != DomainSig::Unary(SortKey::Elem(arg))
            {
                return Err(format!(
                    "`{name}` does not have the expected field shape \
                     (unary fun on the expected sort)"
                ));
            }
            return Ok(d.chid);
        }
        Err(format!("no `{name}` declaration among the swept revisions"))
    };
    let membership = |name: &str, subj_field: &str, subj: Chid| -> Result<Chid, String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            let shape_ok = d.relational
                && d.codomain.is_none()
                && match &d.domain {
                    DomainSig::Record(fields) => matches!(
                        fields.as_slice(),
                        [(f0, SortKey::Elem(s0)), (f1, SortKey::Ground(Ground::Nat))]
                            if f0 == subj_field && f1 == "v" && *s0 == subj
                    ),
                    _ => false,
                };
            if !shape_ok {
                return Err(format!(
                    "`{name}` does not have the expected membership-relation \
                     shape ([{subj_field}: <subject>, v: Nat], relational)"
                ));
            }
            return Ok(d.chid);
        }
        Err(format!("no `{name}` declaration among the swept revisions"))
    };
    let coord = || -> Result<Chid, String> {
        let name = "SimpC/coord";
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            let shape_ok = !d.relational
                && d.codomain == Some(SortKey::Ground(Ground::Q))
                && match &d.domain {
                    DomainSig::Record(fields) => matches!(
                        fields.as_slice(),
                        [
                            (f0, SortKey::Elem(s0)),
                            (f1, SortKey::Ground(Ground::Nat)),
                            (f2, SortKey::Ground(Ground::Nat)),
                        ] if f0 == "complex" && f1 == "j" && f2 == "v" && *s0 == simpc_sort
                    ),
                    _ => false,
                };
            if !shape_ok {
                return Err(format!(
                    "`{name}` does not have the expected coordinate-table shape \
                     ([complex: SimpC, j: Nat, v: Nat] -> Q)"
                ));
            }
            return Ok(d.chid);
        }
        Err(format!("no `{name}` declaration among the swept revisions"))
    };
    Ok(BaryVocab {
        simplex_complex: field("Simplex/complex", simplex_sort, SortKey::Elem(simpc_sort))?,
        simplex_contains: membership("Simplex/contains", "s", simplex_sort)?,
        simpc_n_vertices: field("SimpC/n_vertices", simpc_sort, SortKey::Ground(Ground::Nat))?,
        simpc_amb_dim: field("SimpC/amb_dim", simpc_sort, SortKey::Ground(Ground::Nat))?,
        simpc_coord: coord()?,
        ext_simplex: field(
            "ExtensionSet/simplex",
            ext_sort,
            SortKey::Elem(simplex_sort),
        )?,
        ext_contains: membership("ExtensionSet/contains", "S", ext_sort)?,
    })
}

// ---------------------------------------------------------------------
// Row-context resolution
// ---------------------------------------------------------------------

fn refuse(name: &str, index: usize, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.into(),
        index,
        why,
    }
}

/// The unique value of a unary field fun on `subject`, as a same-body
/// element: zero rows refuse (the element's structure is not in view),
/// conflicting values refuse (functionality-violating territory —
/// never pick), an external value refuses (single-body context).
pub(crate) fn unique_local_field(
    name: &str,
    index: usize,
    rows: &CertRows,
    subject: u32,
    fun: Chid,
    what: &str,
) -> Result<u32, EvalError> {
    let mut found: Option<&Value> = None;
    for row in rows.attrs(subject).iter().filter(|r| r.fun == fun) {
        if row.args.len() != 1 {
            return Err(refuse(
                name,
                index,
                format!(
                    "malformed `{what}` row: expected 1 argument, got {}",
                    row.args.len()
                ),
            ));
        }
        match found {
            None => found = Some(&row.value),
            Some(v) if *v == row.value => {}
            Some(_) => {
                return Err(refuse(
                    name,
                    index,
                    format!("ambiguous `{what}`: conflicting field rows — never picking"),
                ))
            }
        }
    }
    let Some(value) = found else {
        return Err(refuse(
            name,
            index,
            format!("no `{what}` row for the element in view — unresolvable"),
        ));
    };
    let Value::Ref(r) = value else {
        return Err(refuse(
            name,
            index,
            format!("malformed `{what}` row: value is not an element ref"),
        ));
    };
    rows.local(r).ok_or_else(|| {
        refuse(
            name,
            index,
            format!("`{what}` is an external element ref — the row context is single-body"),
        )
    })
}

/// The unique Nat value of a unary field fun on `subject` (same
/// discipline as [`unique_local_field`]).
pub(crate) fn unique_nat_field(
    name: &str,
    index: usize,
    rows: &CertRows,
    subject: u32,
    fun: Chid,
    what: &str,
) -> Result<u64, EvalError> {
    let mut found: Option<u64> = None;
    for row in rows.attrs(subject).iter().filter(|r| r.fun == fun) {
        if row.args.len() != 1 {
            return Err(refuse(
                name,
                index,
                format!(
                    "malformed `{what}` row: expected 1 argument, got {}",
                    row.args.len()
                ),
            ));
        }
        let n = match &row.value {
            Value::Lit(l) => match l.view() {
                LiteralView::Nat(n) => n,
                _ => {
                    return Err(refuse(
                        name,
                        index,
                        format!("malformed `{what}` row: value is not a Nat literal"),
                    ))
                }
            },
            _ => {
                return Err(refuse(
                    name,
                    index,
                    format!("malformed `{what}` row: value is not a Nat literal"),
                ))
            }
        };
        match found {
            None => found = Some(n),
            Some(m) if m == n => {}
            Some(_) => {
                return Err(refuse(
                    name,
                    index,
                    format!("ambiguous `{what}`: conflicting field rows — never picking"),
                ))
            }
        }
    }
    found.ok_or_else(|| {
        refuse(
            name,
            index,
            format!("no `{what}` row for the element in view — unresolvable"),
        )
    })
}

/// The sealed membership mask of `subject` under `contains_rel`,
/// validated against the complex's vertex bound: every membership row
/// must carry a Nat vertex strictly below `bound` (the model's masks
/// are `Fin`-indexed — an out-of-range row corresponds to no model
/// state and refuses), with exactly two arguments. Duplicate rows are
/// harmless (set semantics).
pub(crate) fn membership_mask(
    name: &str,
    index: usize,
    rows: &CertRows,
    subject: u32,
    contains_rel: Chid,
    bound: u64,
    what: &str,
) -> Result<BTreeSet<u64>, EvalError> {
    let mut out = BTreeSet::new();
    for row in rows
        .rel_attrs(subject)
        .iter()
        .filter(|r| r.rel == contains_rel)
    {
        if row.args.len() != 2 {
            return Err(refuse(
                name,
                index,
                format!(
                    "malformed `{what}` membership row: expected 2 arguments, got {}",
                    row.args.len()
                ),
            ));
        }
        let v = match &row.args[1] {
            Value::Lit(l) => match l.view() {
                LiteralView::Nat(v) => v,
                _ => {
                    return Err(refuse(
                        name,
                        index,
                        format!("malformed `{what}` membership row: vertex is not a Nat literal"),
                    ))
                }
            },
            _ => {
                return Err(refuse(
                    name,
                    index,
                    format!("malformed `{what}` membership row: vertex is not a Nat literal"),
                ))
            }
        };
        if v >= bound {
            return Err(refuse(
                name,
                index,
                format!(
                    "`{what}` membership row cites vertex {v}, at or past the complex's \
                     {bound} vertices — outside the spec model's representable masks"
                ),
            ));
        }
        out.insert(v);
    }
    Ok(out)
}

/// The sealed vertex-coordinate table of `complex`: every
/// `SimpC/coord` row on the subject, decoded and validated against the
/// declared bounds (`v < n_vertices`, `j < amb_dim` — the model's
/// coordinate function is `Fin`-indexed, so an out-of-range row
/// corresponds to no model state and refuses). Conflicting duplicates
/// for one `(v, j)` key refuse; agreeing duplicates are harmless.
pub(crate) fn coord_table(
    name: &str,
    index: usize,
    rows: &CertRows,
    v: &BaryVocab,
    complex: u32,
    n_vertices: u64,
    amb_dim: u64,
) -> Result<BTreeMap<(u64, u64), QQ>, EvalError> {
    let mut out: BTreeMap<(u64, u64), QQ> = BTreeMap::new();
    for row in rows
        .attrs(complex)
        .iter()
        .filter(|r| r.fun == v.simpc_coord)
    {
        // Field order is bytewise: `complex`, `j`, `v`.
        if row.args.len() != 3 {
            return Err(refuse(
                name,
                index,
                format!(
                    "malformed `SimpC/coord` row: expected 3 arguments, got {}",
                    row.args.len()
                ),
            ));
        }
        let nat_at = |pos: usize, what: &str| -> Result<u64, EvalError> {
            match &row.args[pos] {
                Value::Lit(l) => match l.view() {
                    LiteralView::Nat(n) => Ok(n),
                    _ => Err(refuse(
                        name,
                        index,
                        format!("malformed `SimpC/coord` row: {what} is not a Nat literal"),
                    )),
                },
                _ => Err(refuse(
                    name,
                    index,
                    format!("malformed `SimpC/coord` row: {what} is not a Nat literal"),
                )),
            }
        };
        let j = nat_at(1, "axis index")?;
        let vert = nat_at(2, "vertex index")?;
        if vert >= n_vertices {
            return Err(refuse(
                name,
                index,
                format!(
                    "`SimpC/coord` row cites vertex {vert}, at or past the complex's \
                     {n_vertices} vertices — outside the spec model's representable states"
                ),
            ));
        }
        if j >= amb_dim {
            return Err(refuse(
                name,
                index,
                format!(
                    "`SimpC/coord` row cites axis {j}, at or past the complex's \
                     ambient dimension {amb_dim} — outside the spec model's representable states"
                ),
            ));
        }
        let q = match &row.value {
            Value::Lit(l) => QQ::from_q_literal(l).ok_or_else(|| {
                refuse(
                    name,
                    index,
                    "malformed `SimpC/coord` row: value is not a canonical Q literal".into(),
                )
            })?,
            _ => {
                return Err(refuse(
                    name,
                    index,
                    "malformed `SimpC/coord` row: value is not a canonical Q literal".into(),
                ))
            }
        };
        match out.get(&(vert, j)) {
            None => {
                out.insert((vert, j), q);
            }
            Some(prev) if *prev == q => {}
            Some(_) => {
                return Err(refuse(
                    name,
                    index,
                    format!(
                        "ambiguous `SimpC/coord` at vertex {vert}, axis {j}: \
                         conflicting rows — never picking"
                    ),
                ))
            }
        }
    }
    Ok(out)
}

// ---------------------------------------------------------------------
// The affine barycentric coordinates (exact rationals)
// ---------------------------------------------------------------------

/// One vertex's barycentric coordinate as an affine function of the
/// ambient coordinate: `λ(x) = slp·x + off`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BaryCoeff {
    pub vertex: u64,
    pub off: QQ,
    pub slp: QQ,
}

/// The one-dimensional barycentric coefficients of a two-vertex
/// simplex — a literal transcription of the Lean `baryCoeffs1D`.
/// `Ok(None)` mirrors the construction's `none` branches (ambient
/// dimension other than one, vertex count other than two, coincident
/// vertex coordinates): a DECIDED outcome for consumers, never a
/// refusal. Refusals arise only from the row decode ([`coord_table`],
/// [`membership_mask`], the field resolvers), whose errors the caller
/// threads through before this function is reached.
pub(crate) fn bary_coeffs_1d(
    name: &str,
    index: usize,
    rows: &CertRows,
    v: &BaryVocab,
    simplex: u32,
) -> Result<Option<[BaryCoeff; 2]>, EvalError> {
    let complex = unique_local_field(
        name,
        index,
        rows,
        simplex,
        v.simplex_complex,
        "Simplex/complex",
    )?;
    let n = unique_nat_field(
        name,
        index,
        rows,
        complex,
        v.simpc_n_vertices,
        "SimpC/n_vertices",
    )?;
    let amb = unique_nat_field(name, index, rows, complex, v.simpc_amb_dim, "SimpC/amb_dim")?;
    let mask = membership_mask(
        name,
        index,
        rows,
        simplex,
        v.simplex_contains,
        n,
        "Simplex/contains",
    )?;
    bary_coeffs_for_mask(name, index, rows, v, complex, n, amb, &mask)
}

/// The construction's geometric tail, shared with the cell-schema
/// conclusion forms (whose masks are the CELLS' own — read from
/// `CellSimplexHasV` rows rather than a `Simplex` element): the
/// coefficients determined by an arbitrary sealed vertex mask over a
/// resolved complex. Same contract as [`bary_coeffs_1d`]: `Ok(None)`
/// mirrors the spec construction's `none` branches; refusals arise
/// only from the row decode.
#[allow(clippy::too_many_arguments)]
pub(crate) fn bary_coeffs_for_mask(
    name: &str,
    index: usize,
    rows: &CertRows,
    v: &BaryVocab,
    complex: u32,
    n: u64,
    amb: u64,
    mask: &BTreeSet<u64>,
) -> Result<Option<[BaryCoeff; 2]>, EvalError> {
    if amb != 1 || mask.len() != 2 {
        return Ok(None);
    }
    let mut it = mask.iter();
    let a = *it.next().expect("two members");
    let b = *it.next().expect("two members");
    let coords = coord_table(name, index, rows, v, complex, n, amb)?;
    let lookup = |vert: u64| -> Result<&QQ, EvalError> {
        coords.get(&(vert, 0)).ok_or_else(|| {
            refuse(
                name,
                index,
                format!(
                    "no `SimpC/coord` row for vertex {vert}, axis 0 — the vertex table \
                     in view is incomplete, unresolvable"
                ),
            )
        })
    };
    let v0 = lookup(a)?.clone();
    let v1 = lookup(b)?.clone();
    if v0 == v1 {
        // The construction's defensive branch: unreachable for a
        // genuine complex (`distinctVerts` with one axis), mirrored
        // verbatim (see the module docs).
        return Ok(None);
    }
    let den = v1.sub(&v0);
    Ok(Some([
        BaryCoeff {
            vertex: a,
            off: qq_div(&v1, &den),
            slp: qq_div(&QQ::from_int(-1), &den),
        },
        BaryCoeff {
            vertex: b,
            off: qq_div(&v0.neg(), &den),
            slp: qq_div(&QQ::one(), &den),
        },
    ]))
}

/// Exact rational division. The divisor must be nonzero — callers
/// divide only by a difference already checked distinct.
pub(crate) fn qq_div(a: &QQ, b: &QQ) -> QQ {
    assert!(!b.is_zero(), "qq_div: zero divisor");
    let mut num = a.num() * BigInt::from(b.den().clone());
    if b.num().sign() == Sign::Minus {
        num = -num;
    }
    QQ::new(num, a.den() * b.num().magnitude())
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

/// The positive primitive-integer rescale of an affine pair — a
/// literal transcription of the Lean `primAffine`. For `c = 0` the
/// result is the sign of `s` paired with zero; otherwise both entries
/// are scaled by the positive rational `lcm(dens)/gcd(scaled nums)`,
/// yielding the unique coprime integer pair with the pair's original
/// orientation.
pub(crate) fn prim_affine(s: &QQ, c: &QQ) -> (QQ, QQ) {
    use num_traits::Zero;
    if c.is_zero() {
        let sign = if s.is_zero() {
            0
        } else if s.is_nonneg() {
            1
        } else {
            -1
        };
        return (QQ::from_int(sign), QQ::zero());
    }
    let g0 = gcd(s.den().clone(), c.den().clone());
    let l: BigUint = s.den() / &g0 * c.den();
    let s_scaled: BigInt = s.num() * BigInt::from(&l / s.den());
    let c_scaled: BigInt = c.num() * BigInt::from(&l / c.den());
    let g = gcd(s_scaled.magnitude().clone(), c_scaled.magnitude().clone());
    debug_assert!(!g.is_zero(), "c is nonzero, so the gcd is positive");
    let k = QQ::new(BigInt::from(l), g);
    (k.mul(s), k.mul(c))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    #[test]
    fn division() {
        assert_eq!(qq_div(&q(1, 2), &q(3, 4)), q(2, 3));
        assert_eq!(qq_div(&q(1, 2), &q(-3, 4)), q(-2, 3));
        assert_eq!(qq_div(&q(-3, 1), &q(-1, 2)), q(6, 1));
        assert_eq!(qq_div(&QQ::zero(), &q(5, 7)), QQ::zero());
    }

    #[test]
    fn prim_affine_zero_offset() {
        assert_eq!(prim_affine(&q(-7, 3), &QQ::zero()), (q(-1, 1), QQ::zero()));
        assert_eq!(prim_affine(&q(2, 5), &QQ::zero()), (q(1, 1), QQ::zero()));
        assert_eq!(
            prim_affine(&QQ::zero(), &QQ::zero()),
            (QQ::zero(), QQ::zero())
        );
    }

    #[test]
    fn prim_affine_scales_to_coprime_integers() {
        // (2, −3): already coprime integers — identity rescale.
        assert_eq!(prim_affine(&q(2, 1), &q(-3, 1)), (q(2, 1), q(-3, 1)));
        // (−2, 2): gcd 2 divides out.
        assert_eq!(prim_affine(&q(-2, 1), &q(2, 1)), (q(-1, 1), q(1, 1)));
        // Fractions: (1/2, −3/4) → lcm 4, scaled (2, −3), gcd 1 → (2, −3).
        assert_eq!(prim_affine(&q(1, 2), &q(-3, 4)), (q(2, 1), q(-3, 1)));
        // Orientation is preserved, never flipped.
        assert_eq!(prim_affine(&q(-1, 2), &q(3, 4)), (q(-2, 1), q(3, 1)));
        // Zero slope with nonzero offset: (0, −5/3) → (0, −1).
        assert_eq!(prim_affine(&QQ::zero(), &q(-5, 3)), (QQ::zero(), q(-1, 1)));
    }
}
