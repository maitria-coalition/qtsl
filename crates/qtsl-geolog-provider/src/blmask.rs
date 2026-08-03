//! The mask family: bounded sweeps over the sealed finite membership
//! data of Simplex/ExtensionSet rows.
//!
//! Six relations. Five are normalization-introduced (they replace
//! forall-iff axiom forms with side-condition premises/conclusions —
//! the theory generator's aux-relation block is their frozen spec);
//! the sixth, `isExtensionSetEmpty`, is the design source's emptiness
//! branch selector, whose polarity is pinned by the registry row's
//! adjudication: **holds iff S is EMPTY** (the declaration comment's
//! word "nonemptiness" is a source typo, contradicted by the
//! relation's name and by the conic/convex axiom guards that consume
//! it).
//!
//! Semantic authority: the Lean catalogue's model (`Simplex.contains :
//! Fin complex.nVertices → Bool`, `ExtensionSet.contains : Fin
//! simplex.complex.nVertices → Bool`, `Simplex.containsNat` /
//! `ExtensionSet.containsNat` / `ExtensionSet.isEmptyB`). Two
//! consequences are load-bearing:
//!
//! - **the mask is the rows, sealed** — a membership row present is a
//!   member, a membership row absent is a non-member; the negative
//!   sweeps (`extensionSetOmits`, `isExtensionSetEmpty`) and the
//!   iff-shaped comparisons are decided against the body's rows as the
//!   complete membership data (the same evaluation class throughout:
//!   bounded computation over a certificate instance's finite data);
//! - **out-of-range membership is unrepresentable** — the Lean masks
//!   are `Fin`-indexed, so a membership row citing a vertex at or past
//!   its complex's `nVertices` corresponds to no model state at all:
//!   such a row REFUSES (never "ignored", which would guess the
//!   spec's extension over states it does not have).
//!
//! One further refusal is deliberate: the comparison relations refuse
//! when their subjects' complexes are ROW-GRAIN DISTINCT elements.
//! The consuming axioms all carry a same-complex (or same-simplex)
//! premise separately, so within their use the guard costs no
//! completeness; across distinct complex elements the row context
//! cannot see chase congruence (two local complex elements may have
//! been equated), and the frozen specs never pin a cross-complex
//! reading — refusal over either guess.
//!
//! Verdict discipline (the crate's): a decided mismatch is
//! `Ok(false)`; unresolvable/ambiguous elements, external references
//! (the row context is single-body), malformed rows, and out-of-range
//! membership REFUSE with a reason, never guessing.

use crate::atomic::elem_local;
use crate::error::EvalError;
use crate::roster::{EntryRow, MaskKind, RelKind};
use crate::rowctx::CertRows;
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use std::collections::BTreeSet;

const F_EXT_OMITS: &[(&str, &str)] = &[("S", "ExtensionSet"), ("v", "Nat")];
const F_EXT_PAIR: &[(&str, &str)] = &[("S1", "ExtensionSet"), ("S2", "ExtensionSet")];
const F_EXT_ONE: &[(&str, &str)] = &[("S", "ExtensionSet")];
const F_FACE_MINUS: &[(&str, &str)] = &[("s", "Simplex"), ("sface", "Simplex"), ("v0", "Nat")];
const F_INTERSECTION: &[(&str, &str)] =
    &[("s1", "Simplex"), ("s2", "Simplex"), ("sint", "Simplex")];
const F_SIMPLEX_PAIR: &[(&str, &str)] = &[("s1", "Simplex"), ("s2", "Simplex")];

/// The mask family's rows of the claimed roster (concatenated at
/// registration — provider.rs). Registration order is part of the
/// seam surface: append at the end, never reorder.
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "extensionSetOmits",
        F_EXT_OMITS,
        RelKind::Mask(MaskKind::ExtOmits),
    ),
    (
        "extensionSetSameMembers",
        F_EXT_PAIR,
        RelKind::Mask(MaskKind::ExtSameMembers),
    ),
    (
        "isExtensionSetEmpty",
        F_EXT_ONE,
        RelKind::Mask(MaskKind::ExtEmpty),
    ),
    (
        "simplexIsFaceMinus",
        F_FACE_MINUS,
        RelKind::Mask(MaskKind::FaceMinus),
    ),
    (
        "simplexIsIntersection",
        F_INTERSECTION,
        RelKind::Mask(MaskKind::Intersection),
    ),
    (
        "simplexSameMembers",
        F_SIMPLEX_PAIR,
        RelKind::Mask(MaskKind::SameMembers),
    ),
];

/// The mask family's resolved vocabulary: the pinned identities of the
/// membership relations and the resolution-chain field funs
/// (`S → simplex → complex → nVertices`), name-selected once at
/// construction and shape-verified (C-ORACLE: names select, shapes
/// verify, identities pin).
#[derive(Debug, Clone)]
pub struct MaskVocab {
    /// `Simplex/complex : Simplex -> SimpC`.
    simplex_complex: Chid,
    /// `Simplex/contains : [s: Simplex, v: Nat]` (relational).
    simplex_contains: Chid,
    /// `SimpC/n_vertices : SimpC -> Nat`.
    simpc_n_vertices: Chid,
    /// `ExtensionSet/simplex : ExtensionSet -> Simplex`.
    ext_simplex: Chid,
    /// `ExtensionSet/contains : [S: ExtensionSet, v: Nat]` (relational).
    ext_contains: Chid,
}

/// Build the mask vocabulary over the declared indices. `Err` → the
/// family is not claimed (declared-but-unbound, safe-fail).
pub fn build_mask_vocab(
    indices: &[&TheoryIndex],
    simplex_sort: Chid,
    ext_sort: Chid,
    simpc_sort: Chid,
) -> Result<MaskVocab, String> {
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
    Ok(MaskVocab {
        simplex_complex: field("Simplex/complex", simplex_sort, SortKey::Elem(simpc_sort))?,
        simplex_contains: membership("Simplex/contains", "s", simplex_sort)?,
        simpc_n_vertices: field("SimpC/n_vertices", simpc_sort, SortKey::Ground(Ground::Nat))?,
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
/// conflicting values refuse (functionality-violating territory the
/// projection rejects — never pick), an external value refuses (its
/// own field rows live in another body).
fn unique_local_field(
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
fn unique_nat_field(
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
/// must carry a Nat vertex strictly below `bound` (the Lean masks are
/// `Fin`-indexed — an out-of-range row corresponds to no model state
/// and refuses), with exactly two arguments. Duplicate rows are
/// harmless (set semantics).
fn mask(
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

/// Resolve a simplex argument's complex element (`Simplex/complex`).
fn complex_of_simplex(
    name: &str,
    index: usize,
    rows: &CertRows,
    v: &MaskVocab,
    s: u32,
) -> Result<u32, EvalError> {
    unique_local_field(name, index, rows, s, v.simplex_complex, "Simplex/complex")
}

/// Resolve an extension-set argument's simplex, then its complex.
fn complex_of_ext(
    name: &str,
    index: usize,
    rows: &CertRows,
    v: &MaskVocab,
    ext: u32,
) -> Result<u32, EvalError> {
    let sx = unique_local_field(
        name,
        index,
        rows,
        ext,
        v.ext_simplex,
        "ExtensionSet/simplex",
    )?;
    complex_of_simplex(name, index, rows, v, sx)
}

/// The complex's vertex count (`SimpC/n_vertices`).
fn n_vertices(
    name: &str,
    index: usize,
    rows: &CertRows,
    v: &MaskVocab,
    complex: u32,
) -> Result<u64, EvalError> {
    unique_nat_field(
        name,
        index,
        rows,
        complex,
        v.simpc_n_vertices,
        "SimpC/n_vertices",
    )
}

/// Refuse unless every listed complex element is the SAME local
/// element as the first (row-grain identity; see the module docs on
/// why distinct elements refuse rather than compare).
fn require_same_complex(name: &str, complexes: &[(usize, u32)]) -> Result<u32, EvalError> {
    let (_, c0) = complexes[0];
    for (index, c) in &complexes[1..] {
        if *c != c0 {
            return Err(refuse(
                name,
                *index,
                "row-grain distinct complex elements — chase congruence is not in view \
                 here, and the spec pins no cross-complex reading; refusing over a guess"
                    .into(),
            ));
        }
    }
    Ok(c0)
}

fn nat_arg(name: &str, index: usize, val: &Value) -> Result<u64, EvalError> {
    let Value::Lit(l) = val else {
        return Err(EvalError::ArgDtype {
            name: name.into(),
            index,
            expected: "Nat",
            found: 0xFF,
        });
    };
    let LiteralView::Nat(n) = l.view() else {
        return Err(EvalError::ArgDtype {
            name: name.into(),
            index,
            expected: "Nat",
            found: l.dtype_code(),
        });
    };
    Ok(n)
}

// ---------------------------------------------------------------------
// Dispatch
// ---------------------------------------------------------------------

/// Evaluate a mask-family relation. Argument cells arrive in declared
/// (bytewise) field order — the entry tables above.
pub(crate) fn eval_mask(
    name: &str,
    v: &MaskVocab,
    kind: MaskKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    match kind {
        MaskKind::ExtOmits => {
            // Field order: S, v.
            let s = elem_local(name, 0, args[0], rows)?;
            let vertex = nat_arg(name, 1, args[1])?;
            let c = complex_of_ext(name, 0, rows, v, s)?;
            let n = n_vertices(name, 0, rows, v, c)?;
            let m = mask(name, 0, rows, s, v.ext_contains, n, "ExtensionSet/contains")?;
            // A vertex at or past the bound is outside every mask
            // (`containsNat` is false there), so omission holds for it.
            Ok(!m.contains(&vertex))
        }
        MaskKind::ExtSameMembers => {
            let s1 = elem_local(name, 0, args[0], rows)?;
            let s2 = elem_local(name, 1, args[1], rows)?;
            let c1 = complex_of_ext(name, 0, rows, v, s1)?;
            let c2 = complex_of_ext(name, 1, rows, v, s2)?;
            let c = require_same_complex(name, &[(0, c1), (1, c2)])?;
            let n = n_vertices(name, 0, rows, v, c)?;
            let m1 = mask(
                name,
                0,
                rows,
                s1,
                v.ext_contains,
                n,
                "ExtensionSet/contains",
            )?;
            let m2 = mask(
                name,
                1,
                rows,
                s2,
                v.ext_contains,
                n,
                "ExtensionSet/contains",
            )?;
            Ok(m1 == m2)
        }
        MaskKind::ExtEmpty => {
            // Holds iff the mask is EMPTY (the pinned polarity).
            let s = elem_local(name, 0, args[0], rows)?;
            let c = complex_of_ext(name, 0, rows, v, s)?;
            let n = n_vertices(name, 0, rows, v, c)?;
            let m = mask(name, 0, rows, s, v.ext_contains, n, "ExtensionSet/contains")?;
            Ok(m.is_empty())
        }
        MaskKind::FaceMinus => {
            // Field order: s, sface, v0. Spec: sface's mask == s's
            // mask minus {v0}.
            let s = elem_local(name, 0, args[0], rows)?;
            let sface = elem_local(name, 1, args[1], rows)?;
            let v0 = nat_arg(name, 2, args[2])?;
            let cs = complex_of_simplex(name, 0, rows, v, s)?;
            let cf = complex_of_simplex(name, 1, rows, v, sface)?;
            let c = require_same_complex(name, &[(0, cs), (1, cf)])?;
            let n = n_vertices(name, 0, rows, v, c)?;
            let ms = mask(name, 0, rows, s, v.simplex_contains, n, "Simplex/contains")?;
            let mf = mask(
                name,
                1,
                rows,
                sface,
                v.simplex_contains,
                n,
                "Simplex/contains",
            )?;
            let mut expected = ms;
            expected.remove(&v0);
            Ok(mf == expected)
        }
        MaskKind::Intersection => {
            // Field order: s1, s2, sint. Spec: sint's mask == s1's
            // mask ∩ s2's mask.
            let s1 = elem_local(name, 0, args[0], rows)?;
            let s2 = elem_local(name, 1, args[1], rows)?;
            let sint = elem_local(name, 2, args[2], rows)?;
            let c1 = complex_of_simplex(name, 0, rows, v, s1)?;
            let c2 = complex_of_simplex(name, 1, rows, v, s2)?;
            let ci = complex_of_simplex(name, 2, rows, v, sint)?;
            let c = require_same_complex(name, &[(0, c1), (1, c2), (2, ci)])?;
            let n = n_vertices(name, 0, rows, v, c)?;
            let m1 = mask(name, 0, rows, s1, v.simplex_contains, n, "Simplex/contains")?;
            let m2 = mask(name, 1, rows, s2, v.simplex_contains, n, "Simplex/contains")?;
            let mi = mask(
                name,
                2,
                rows,
                sint,
                v.simplex_contains,
                n,
                "Simplex/contains",
            )?;
            let inter: BTreeSet<u64> = m1.intersection(&m2).copied().collect();
            Ok(mi == inter)
        }
        MaskKind::SameMembers => {
            let s1 = elem_local(name, 0, args[0], rows)?;
            let s2 = elem_local(name, 1, args[1], rows)?;
            let c1 = complex_of_simplex(name, 0, rows, v, s1)?;
            let c2 = complex_of_simplex(name, 1, rows, v, s2)?;
            let c = require_same_complex(name, &[(0, c1), (1, c2)])?;
            let n = n_vertices(name, 0, rows, v, c)?;
            let m1 = mask(name, 0, rows, s1, v.simplex_contains, n, "Simplex/contains")?;
            let m2 = mask(name, 1, rows, s2, v.simplex_contains, n, "Simplex/contains")?;
            Ok(m1 == m2)
        }
    }
}
