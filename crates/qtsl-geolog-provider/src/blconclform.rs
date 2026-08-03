//! The conclusion-form family: bounded checks that a `Formula` element
//! IS a specific formula constructed from certificate geometry —
//! `barycentricHalfspaceForm` (the region-atom rules'
//! barycentric-halfspace conjunction), the four cell-schema forms
//! (`cellStrictInteriorForm`, `cellOneHotForm`, `cellOutWitnessForm`,
//! `cellOutZeroForm` — the cell rules' conclusion syntax, sharing one
//! arity/range gate over the destructured cell application), and
//! `lirpaConclusionForm` (the LiRPA relaxation rule's conclusion
//! shape).
//!
//! Semantic authority: the Lean catalogue's `barycentricHalfspaceForm`
//! (`lean/qtsl/Qtsl/Core/Catalogue.lean`), which holds exactly when
//! `barycentricHalfspaceBuild t simplex S = some F`. The design
//! source's declaration comment states the conjunction as
//!
//! ```text
//!   AND_{i in S} λ_i(t) <= 0   AND   AND_{i notin S} λ_i(t) >= 0
//! ```
//!
//! and the realized build pins one canonical rendering of it (the
//! producers' all-`le` form): per vertex, in increasing vertex order,
//! one atom `canon(±λ_v)(t) <= 0` — the `+` orientation for vertices
//! in `S`, the `−` orientation (folding the `>= 0` reading into the
//! `le` comparator) for vertices outside it — where `canon` is the
//! positive primitive-integer rescale (`primAffine`) and the left-hand
//! term is laid out as `s'·t` when the rescaled offset is zero and
//! `s'·t + c'` otherwise, constants on the pinned sides. The two atoms
//! join in a single `FAnd`. "Is" means STRUCTURAL equality over the
//! constructor rows, exactly as in [`crate::atomic`].
//!
//! Two verdict notes, both inherited from the authority:
//!
//! - the build's `none` branches (ambient dimension ≠ 1, vertex count
//!   ≠ 2, coincident vertex coordinates — see [`crate::barycoord`]) make
//!   the relation a decided `false` for EVERY formula argument;
//! - the build guards `S.simplex = simplex`. At row grain that guard
//!   is decidable only when the extension set's simplex is the SAME
//!   local element as the simplex argument (chase congruence is not in
//!   view here, and two row-grain-distinct elements may or may not
//!   denote one model simplex) — distinct elements REFUSE rather than
//!   guess in either direction. The consuming axioms pass the
//!   extension set's own simplex, so the guard costs no completeness
//!   within their use.
//!
//! # The cell-schema forms
//!
//! Semantic authority: the Lean catalogue's `cellStrictInteriorForm` /
//! `cellOneHotForm` / `cellOutWitnessForm` / `cellOutZeroForm`, each
//! holding exactly when its build returns `some F`. The spec-grain
//! warning inherited from this family's opener applies with force: the
//! design source's prose states the SEMANTIC conjunction, but the
//! realized builds pin a rendering that differs from the halfspace
//! form's canonicalization on every axis —
//!
//! - λ-atoms carry the RAW `baryLambdas1D` terms, laid out
//!   `TAdd(TConst(c), TMul(TConst(s), TVar(input)))`: constant on the
//!   LEFT of the sum, NO positive primitive-integer rescale, NO bare-
//!   product special case at `c = 0`;
//! - comparators are strict and sign-directed per the cell's extension
//!   mask (strict interior: `< 0` extended / `> 0` core; the out-
//!   witness atom REVERSES both);
//! - the indicator forms chain by `Formula.chainAnd` (`[] → FTrue`,
//!   `[f] → f`, cons → nested `FAnd`), so a single-cell schema reads
//!   `(b_0 = 1) AND FTrue` while a two-cell schema's second arm is the
//!   bare atom.
//!
//! The shared gate (frozen spec, designv3 declaration comment): each
//! relation destructures the cell application — its input wire and its
//! dense output-wire list, read from the `InputPort`/`OutputPort` rows
//! — and REJECTS unless the cell index is in range of the schema's
//! cells and the output arity equals the schema's cell count. REJECT
//! is the build's `none` reading: a decided `false` (the relation's
//! extension over `Nat` indices is the image of its `Fin`-indexed spec
//! instances — out-of-range tuples are simply not in it), exactly as
//! the out-witness form's own mask guard decides `false`. The schema's
//! cells at row grain are the certificate extension's rows —
//! `SimpC/nCells` plus the `CellSimplexHasV`/`CellExtHasV` mask
//! relations, validated against the declared bounds like every other
//! sealed mask in this crate.
//!
//! Two refusal classes are deliberately NOT decided verdicts: an app
//! whose port rows do not destructure as a cell application's (no
//! input port in view, positions not dense, conflicting wires at one
//! position) — the frozen spec is silent there, and the consuming
//! axioms guarantee `PrimApp/prim = PCell` separately — and the usual
//! row pathology (unresolvable/ambiguous elements, external refs,
//! malformed rows, out-of-range mask/coordinate rows).
//!
//! # The LiRPA conclusion form
//!
//! Semantic authority: the Lean catalogue's `lirpaConclusionForm` —
//! a plain equality with the build, no geometry in sight:
//!
//! ```text
//!   F = FAnd(FAtomLE(affineWireTerm β α preact, TVar(post)),
//!            FAtomLE(TVar(post), affineWireTerm δ γ preact))
//!   affineWireTerm offset slope w
//!     = TAdd(TConst(offset), TMul(TConst(slope), TVar(w)))
//! ```
//!
//! — the two-sided ReLU relaxation `α·h + β ≤ post ≤ γ·h + δ` around
//! `post = relu(preact)`, rendered in the `affineWireTerm` layout:
//! offset FIRST in the sum, constants on the LEFT of the product, NO
//! zero special cases (β = 0 still reads `TAdd(TConst(0), …)`), lower
//! atom's affine on the LEFT of `le`, upper atom's on the RIGHT. The
//! kernel-checked anchor is the executable demo's `pfLirpa`
//! (`lean/qtsl/Qtsl/Core/DemoData.lean`), whose `postForm` premise is
//! discharged by `rfl` against exactly this build.
//!
//! Scope note: this relation is the conclusion's SHAPE only. The
//! rule's semantic side conditions — `reluLinked`, the sign
//! constraints on `a`, `b`, and the six endpoint inequalities — are
//! separate premises of `PLiRPAData`, discharged by other rows; no
//! part of them is (or may soundly be) folded in here. In particular
//! `post = preact` claims evaluate on shape like any other: the
//! degenerate build holds when the formula matches, and the ReLU link
//! premise is where such a state would fail.
//!
//! The wires compare NOMINALLY (local or external element refs — the
//! same normalization as the cell forms' port wires); the four
//! rationals compare as exact canonical `Q`. Non-`Q` rational cells
//! and non-ref wire cells REFUSE (argument pathology, not a decided
//! mismatch); everything structural below the formula head decides
//! `false` on mismatch under the crate's usual walk discipline.
//!
//! Verdict discipline (the crate's): a decided mismatch is
//! `Ok(false)`; unresolvable or ambiguous elements, external
//! references, malformed rows, incomplete vertex tables, and
//! out-of-range membership or coordinate rows REFUSE with a reason,
//! never guessing.

use crate::barycoord::{
    bary_coeffs_1d, bary_coeffs_for_mask, prim_affine, unique_local_field, unique_nat_field,
    BaryCoeff, BaryVocab,
};
use crate::error::EvalError;
use crate::formrows::{BlVocab, FormCtor, TermCtor, Walk};
use crate::qq::QQ;
use crate::roster::{ConclFormKind, EntryRow, RelKind};
use crate::rowctx::CertRows;
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use std::collections::{BTreeMap, BTreeSet};

const F_BARY_HALFSPACE: &[(&str, &str)] = &[
    ("S", "ExtensionSet"),
    ("formula", "Formula"),
    ("simplex", "Simplex"),
    ("t", "Term"),
];

const F_CELL_WHICH_I: &[(&str, &str)] = &[
    ("app", "PrimApp"),
    ("formula", "Formula"),
    ("schema", "SimpC"),
    ("whichI", "Nat"),
];

const F_CELL_OUT_WITNESS: &[(&str, &str)] = &[
    ("app", "PrimApp"),
    ("formula", "Formula"),
    ("schema", "SimpC"),
    ("whichJ", "Nat"),
    ("witnessVertex", "Nat"),
];

const F_CELL_OUT_ZERO: &[(&str, &str)] = &[
    ("app", "PrimApp"),
    ("formula", "Formula"),
    ("schema", "SimpC"),
    ("whichJ", "Nat"),
];

/// Registry (bytewise) field order — NOT the theory declaration's
/// `[preact, post, alpha, beta, gamma, delta, formula]`. The claim
/// order fixes the evaluator's argument order; copy from the registry
/// row, as the census instructs.
const F_LIRPA: &[(&str, &str)] = &[
    ("alpha", "Q"),
    ("beta", "Q"),
    ("delta", "Q"),
    ("formula", "Formula"),
    ("gamma", "Q"),
    ("post", "Wire"),
    ("preact", "Wire"),
];

/// The conclusion-form family's rows of the claimed roster
/// (concatenated at registration — provider.rs). Registration order is
/// part of the seam surface: append at the end, never reorder.
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "barycentricHalfspaceForm",
        F_BARY_HALFSPACE,
        RelKind::ConclForm(ConclFormKind::BarycentricHalfspace),
    ),
    (
        "cellStrictInteriorForm",
        F_CELL_WHICH_I,
        RelKind::ConclForm(ConclFormKind::CellStrictInterior),
    ),
    (
        "cellOneHotForm",
        F_CELL_WHICH_I,
        RelKind::ConclForm(ConclFormKind::CellOneHot),
    ),
    (
        "cellOutWitnessForm",
        F_CELL_OUT_WITNESS,
        RelKind::ConclForm(ConclFormKind::CellOutWitness),
    ),
    (
        "cellOutZeroForm",
        F_CELL_OUT_ZERO,
        RelKind::ConclForm(ConclFormKind::CellOutZero),
    ),
    (
        "lirpaConclusionForm",
        F_LIRPA,
        RelKind::ConclForm(ConclFormKind::Lirpa),
    ),
];

// ---------------------------------------------------------------------
// The cell-application vocabulary
// ---------------------------------------------------------------------

/// The cell-schema forms' resolved vocabulary: the hypernet port
/// fields (the app destructure) plus the certificate extension's
/// cell-list rows (`SimpC/nCells`, the two cell-mask relations) —
/// name-selected once at construction and shape-verified, exactly as
/// [`crate::barycoord::BaryVocab`].
#[derive(Debug, Clone)]
pub struct CellAppVocab {
    /// `InputPort/app : InputPort -> PrimApp`.
    pub(crate) input_app: Chid,
    /// `InputPort/pos : InputPort -> Nat`.
    pub(crate) input_pos: Chid,
    /// `InputPort/wire : InputPort -> Wire`.
    pub(crate) input_wire: Chid,
    /// `OutputPort/app : OutputPort -> PrimApp`.
    pub(crate) output_app: Chid,
    /// `OutputPort/pos : OutputPort -> Nat`.
    pub(crate) output_pos: Chid,
    /// `OutputPort/wire : OutputPort -> Wire`.
    pub(crate) output_wire: Chid,
    /// `SimpC/nCells : SimpC -> Nat` (certificate extension).
    pub(crate) simpc_n_cells: Chid,
    /// `CellSimplexHasV : [cell: Nat, complex: SimpC, v: Nat]`
    /// (relational — vertex `v` is in cell `cell`'s simplex mask).
    pub(crate) cell_simplex_has_v: Chid,
    /// `CellExtHasV : [cell: Nat, complex: SimpC, v: Nat]`
    /// (relational — vertex `v` is in cell `cell`'s extension mask).
    pub(crate) cell_ext_has_v: Chid,
}

/// Build the cell-application vocabulary over the declared indices.
/// `Err` → the cell-schema forms are not claimed
/// (declared-but-unbound, safe-fail); the halfspace form's claim is
/// unaffected.
pub fn build_cellapp_vocab(
    indices: &[&TheoryIndex],
    input_port_sort: Chid,
    output_port_sort: Chid,
    primapp_sort: Chid,
    wire_sort: Chid,
    simpc_sort: Chid,
) -> Result<CellAppVocab, String> {
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
    let cell_mask_rel = |name: &str| -> Result<Chid, String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            let shape_ok = d.relational
                && d.codomain.is_none()
                && match &d.domain {
                    DomainSig::Record(fields) => matches!(
                        fields.as_slice(),
                        [
                            (f0, SortKey::Ground(Ground::Nat)),
                            (f1, SortKey::Elem(s1)),
                            (f2, SortKey::Ground(Ground::Nat)),
                        ] if f0 == "cell" && f1 == "complex" && f2 == "v" && *s1 == simpc_sort
                    ),
                    _ => false,
                };
            if !shape_ok {
                return Err(format!(
                    "`{name}` does not have the expected cell-mask shape \
                     ([cell: Nat, complex: SimpC, v: Nat], relational)"
                ));
            }
            return Ok(d.chid);
        }
        Err(format!("no `{name}` declaration among the swept revisions"))
    };
    Ok(CellAppVocab {
        input_app: field(
            "InputPort/app",
            input_port_sort,
            SortKey::Elem(primapp_sort),
        )?,
        input_pos: field(
            "InputPort/pos",
            input_port_sort,
            SortKey::Ground(Ground::Nat),
        )?,
        input_wire: field("InputPort/wire", input_port_sort, SortKey::Elem(wire_sort))?,
        output_app: field(
            "OutputPort/app",
            output_port_sort,
            SortKey::Elem(primapp_sort),
        )?,
        output_pos: field(
            "OutputPort/pos",
            output_port_sort,
            SortKey::Ground(Ground::Nat),
        )?,
        output_wire: field(
            "OutputPort/wire",
            output_port_sort,
            SortKey::Elem(wire_sort),
        )?,
        simpc_n_cells: field("SimpC/nCells", simpc_sort, SortKey::Ground(Ground::Nat))?,
        cell_simplex_has_v: cell_mask_rel("CellSimplexHasV")?,
        cell_ext_has_v: cell_mask_rel("CellExtHasV")?,
    })
}

/// Evaluate a conclusion-form relation. Argument cells arrive in
/// declared (bytewise) field order — the entry table above. `bv` is
/// `Some` for every claimed geometry-reading entry and `cav` for
/// every claimed cell-schema entry (construction invariant of the
/// provider: a claim without its vocabulary is unconstructible; the
/// LiRPA form reads no geometry and needs neither).
pub(crate) fn eval_conclform(
    name: &str,
    blv: &BlVocab,
    bv: Option<&BaryVocab>,
    cav: Option<&CellAppVocab>,
    kind: ConclFormKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    match kind {
        ConclFormKind::Lirpa => eval_lirpa(name, blv, args, rows),
        ConclFormKind::CellStrictInterior
        | ConclFormKind::CellOneHot
        | ConclFormKind::CellOutWitness
        | ConclFormKind::CellOutZero => {
            let bv = bv.expect("claimed implies vocabulary");
            let cav = cav.expect("claimed implies vocabulary");
            eval_cell_form(name, blv, bv, cav, kind, args, rows)
        }
        ConclFormKind::BarycentricHalfspace => {
            let bv = bv.expect("claimed implies vocabulary");
            let mut w = Walk::new(name, blv, rows);
            // Field order: S, formula, simplex, t.
            let s_ext = w.local(0, args[0])?;
            let formula = w.local(1, args[1])?;
            let simplex = w.local(2, args[2])?;
            let t = w.local(3, args[3])?;

            // The build's `S.simplex = simplex` guard, at row grain
            // (module docs: same element passes, distinct refuses).
            let s_simplex =
                unique_local_field(name, 0, rows, s_ext, bv.ext_simplex, "ExtensionSet/simplex")?;
            if s_simplex != simplex {
                return Err(EvalError::CtxArg {
                    name: name.into(),
                    index: 0,
                    why: "the extension set's simplex and the simplex argument are \
                          row-grain distinct elements — chase congruence is not in view \
                          here, so the same-simplex guard is undecidable; refusing over \
                          a guess"
                        .into(),
                });
            }

            // The barycentric coefficients (a decided `false` on the
            // build's `none` branches).
            let Some(coeffs) = bary_coeffs_1d(name, 2, rows, bv, simplex)? else {
                return Ok(false);
            };

            // The extension mask, bounded by the same vertex count the
            // coefficients were derived under.
            let complex = unique_local_field(
                name,
                2,
                rows,
                simplex,
                bv.simplex_complex,
                "Simplex/complex",
            )?;
            let n = crate::barycoord::unique_nat_field(
                name,
                2,
                rows,
                complex,
                bv.simpc_n_vertices,
                "SimpC/n_vertices",
            )?;
            let emask = crate::barycoord::membership_mask(
                name,
                0,
                rows,
                s_ext,
                bv.ext_contains,
                n,
                "ExtensionSet/contains",
            )?;

            // Expected rescaled atom constants, in vertex order.
            let expected: Vec<(QQ, QQ)> = coeffs
                .iter()
                .map(|c| {
                    if emask.contains(&c.vertex) {
                        prim_affine(&c.slp, &c.off)
                    } else {
                        prim_affine(&c.slp.neg(), &c.off.neg())
                    }
                })
                .collect();

            // formula = FAnd(atom₀, atom₁), arms in vertex order.
            let (head, head_row) = w.form_ctor_row(1, formula)?;
            if head != FormCtor::And {
                return Ok(false);
            }
            let arm0 = w.local(1, &head_row.args[0])?;
            let arm1 = w.local(1, &head_row.args[1])?;
            Ok(halfspace_atom(&mut w, arm0, &expected[0], t)?
                && halfspace_atom(&mut w, arm1, &expected[1], t)?)
        }
    }
}

/// One halfspace atom: `FAtomLE(lhs, TConst(0))` with
/// `lhs = TMul(TConst(s'), t)` when `c' = 0` and
/// `lhs = TAdd(TMul(TConst(s'), t), TConst(c'))` otherwise, the term
/// argument compared structurally.
fn halfspace_atom(
    w: &mut Walk<'_>,
    atom: u32,
    scaled: &(QQ, QQ),
    t: u32,
) -> Result<bool, EvalError> {
    let (s_prime, c_prime) = scaled;
    let (k, row) = w.form_ctor_row(1, atom)?;
    if k != FormCtor::Atom(1) {
        // 1 = the `le` comparator; any other head is a decided mismatch.
        return Ok(false);
    }
    // Right arm: the canonical rational zero.
    let r = w.local(1, &row.args[1])?;
    let (rk, r_row) = w.term_ctor_row(1, r)?;
    if rk != TermCtor::Const || !w.const_value(1, r_row)?.is_zero() {
        return Ok(false);
    }
    // Left arm.
    let l = w.local(1, &row.args[0])?;
    if c_prime.is_zero() {
        scaled_term(w, l, s_prime, t)
    } else {
        let (lk, l_row) = w.term_ctor_row(1, l)?;
        if lk != TermCtor::Add {
            return Ok(false);
        }
        let sum_l = w.local(1, &l_row.args[0])?;
        let sum_r = w.local(1, &l_row.args[1])?;
        if !scaled_term(w, sum_l, s_prime, t)? {
            return Ok(false);
        }
        let (ck, c_row) = w.term_ctor_row(1, sum_r)?;
        if ck != TermCtor::Const {
            return Ok(false);
        }
        Ok(w.const_value(1, c_row)? == *c_prime)
    }
}

/// `TMul(TConst(s'), t)` — the constant on the left, the term argument
/// compared structurally.
fn scaled_term(w: &mut Walk<'_>, elem: u32, s_prime: &QQ, t: u32) -> Result<bool, EvalError> {
    let (k, row) = w.term_ctor_row(1, elem)?;
    if k != TermCtor::Mul {
        return Ok(false);
    }
    let coeff = w.local(1, &row.args[0])?;
    let (ck, c_row) = w.term_ctor_row(1, coeff)?;
    if ck != TermCtor::Const || w.const_value(1, c_row)? != *s_prime {
        return Ok(false);
    }
    let arg = w.local(1, &row.args[1])?;
    w.struct_eq(1, arg, t, true)
}

// ---------------------------------------------------------------------
// The cell-schema forms
// ---------------------------------------------------------------------

/// `FAtom` comparator codes (the pinned bowtie order — formrows):
/// `LT = 0`, `LE = 1`, `EQ = 2`, `GE = 3`, `GT = 4` (`GE` joined with
/// the NN conclusion-form port — [`crate::nnform`]).
pub(crate) const ATOM_LT: u8 = 0;
pub(crate) const ATOM_LE: u8 = 1;
pub(crate) const ATOM_EQ: u8 = 2;
pub(crate) const ATOM_GE: u8 = 3;
pub(crate) const ATOM_GT: u8 = 4;

fn refuse(name: &str, index: usize, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.into(),
        index,
        why,
    }
}

/// A `Nat` literal argument cell (the `whichI`/`whichJ`/
/// `witnessVertex` fields).
fn nat_arg(name: &str, index: usize, v: &Value) -> Result<u64, EvalError> {
    let Value::Lit(l) = v else {
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

/// The unique field row's value on `subject`, kept as the raw `Value`
/// and required to be an element ref (local or external — the port
/// wires compare nominally, which normalizes both). Zero rows refuse
/// (structure not in view), conflicting values refuse (never pick).
fn unique_ref_field(
    name: &str,
    index: usize,
    rows: &CertRows,
    subject: u32,
    fun: Chid,
    what: &str,
) -> Result<Value, EvalError> {
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
    if !matches!(value, Value::Ref(_)) {
        return Err(refuse(
            name,
            index,
            format!("malformed `{what}` row: value is not an element ref"),
        ));
    }
    Ok(value.clone())
}

/// Destructure the cell application: its input wire (the unique input
/// port at position 0) and its dense output-wire list (positions
/// exactly `0..m-1`, in order). Port rows are the sealed finite data
/// of the app in view; a port set that does not destructure as a cell
/// application's REFUSES (the frozen spec is silent there — the
/// consuming axioms pin `PrimApp/prim = PCell` separately), as do
/// conflicting wires at one position (the port-uniqueness axiom would
/// equate the port elements, so agreeing duplicates are harmless).
fn destructure_cell_app(
    name: &str,
    rows: &CertRows,
    cav: &CellAppVocab,
    app: u32,
) -> Result<(Value, Vec<Value>), EvalError> {
    let mut in_ports: BTreeMap<u64, Value> = BTreeMap::new();
    let mut out_ports: BTreeMap<u64, Value> = BTreeMap::new();
    // A port's `…/app` row has the PORT as its subject and the app as
    // its VALUE — the constructor-direction index reaches the ports.
    for row in rows.producers(app) {
        let is_in = row.fun == cav.input_app;
        let is_out = row.fun == cav.output_app;
        if !is_in && !is_out {
            continue;
        }
        let side = if is_in { "InputPort" } else { "OutputPort" };
        if row.args.len() != 1 {
            return Err(refuse(
                name,
                0,
                format!(
                    "malformed `{side}/app` row: expected 1 argument, got {}",
                    row.args.len()
                ),
            ));
        }
        let port = match &row.args[0] {
            Value::Ref(r) => rows.local(r).ok_or_else(|| {
                refuse(
                    name,
                    0,
                    format!("`{side}/app` cites an external port element — single-body context"),
                )
            })?,
            _ => {
                return Err(refuse(
                    name,
                    0,
                    format!("malformed `{side}/app` row: port position is not an element ref"),
                ))
            }
        };
        let (pos_fun, wire_fun) = if is_in {
            (cav.input_pos, cav.input_wire)
        } else {
            (cav.output_pos, cav.output_wire)
        };
        let pos = unique_nat_field(name, 0, rows, port, pos_fun, &format!("{side}/pos"))?;
        let wire = unique_ref_field(name, 0, rows, port, wire_fun, &format!("{side}/wire"))?;
        let map = if is_in { &mut in_ports } else { &mut out_ports };
        match map.get(&pos) {
            None => {
                map.insert(pos, wire);
            }
            Some(prev) if *prev == wire => {}
            Some(_) => {
                return Err(refuse(
                    name,
                    0,
                    format!(
                        "conflicting `{side}` wires at position {pos} — the port-uniqueness \
                         axiom admits no such state; never picking"
                    ),
                ))
            }
        }
    }
    if in_ports.len() != 1 || !in_ports.contains_key(&0) {
        return Err(refuse(
            name,
            0,
            format!(
                "the app's input ports in view ({} port(s)) do not destructure as a cell \
                 application's (exactly one input port, at position 0)",
                in_ports.len()
            ),
        ));
    }
    let input = in_ports.remove(&0).expect("checked present");
    let mut outputs = Vec::with_capacity(out_ports.len());
    for (i, (pos, wire)) in out_ports.into_iter().enumerate() {
        if pos != i as u64 {
            return Err(refuse(
                name,
                0,
                format!(
                    "output port positions are not the dense list 0..m-1 (gap below \
                     position {pos}) — no cell-application state corresponds"
                ),
            ));
        }
        outputs.push(wire);
    }
    Ok((input, outputs))
}

/// The schema's sealed cell masks: every `CellSimplexHasV` /
/// `CellExtHasV` row citing `schema`, validated against the declared
/// bounds (`cell < n_cells`, `v < n_vertices` — the spec model's masks
/// are `Fin`-indexed, so an out-of-range row corresponds to no model
/// state and refuses). Returns (simplex masks, extension masks), each
/// keyed by cell index.
type CellMasks = (BTreeMap<u64, BTreeSet<u64>>, BTreeMap<u64, BTreeSet<u64>>);
fn cell_masks(
    name: &str,
    rows: &CertRows,
    cav: &CellAppVocab,
    schema: u32,
    n_cells: u64,
    n_vertices: u64,
) -> Result<CellMasks, EvalError> {
    let mut simp: BTreeMap<u64, BTreeSet<u64>> = BTreeMap::new();
    let mut ext: BTreeMap<u64, BTreeSet<u64>> = BTreeMap::new();
    for row in rows.rel_rows_citing(schema) {
        let (target, what) = if row.rel == cav.cell_simplex_has_v {
            (&mut simp, "CellSimplexHasV")
        } else if row.rel == cav.cell_ext_has_v {
            (&mut ext, "CellExtHasV")
        } else {
            continue;
        };
        // Wire field order (bytewise): cell, complex, v.
        if row.args.len() != 3 {
            return Err(refuse(
                name,
                2,
                format!(
                    "malformed `{what}` row: expected 3 arguments, got {}",
                    row.args.len()
                ),
            ));
        }
        let nat_at = |pos: usize, field: &str| -> Result<u64, EvalError> {
            match &row.args[pos] {
                Value::Lit(l) => match l.view() {
                    LiteralView::Nat(n) => Ok(n),
                    _ => Err(refuse(
                        name,
                        2,
                        format!("malformed `{what}` row: {field} is not a Nat literal"),
                    )),
                },
                _ => Err(refuse(
                    name,
                    2,
                    format!("malformed `{what}` row: {field} is not a Nat literal"),
                )),
            }
        };
        let cell = nat_at(0, "cell index")?;
        let v = nat_at(2, "vertex index")?;
        // Citation only guarantees membership — verify the complex
        // position actually is this schema (with Nat cells at 0 and 2
        // it must be, but verify rather than infer).
        let cited = match &row.args[1] {
            Value::Ref(r) => rows.local(r),
            _ => None,
        };
        if cited != Some(schema) {
            continue;
        }
        if cell >= n_cells {
            return Err(refuse(
                name,
                2,
                format!(
                    "`{what}` row cites cell {cell}, at or past the schema's {n_cells} \
                     cells — outside the spec model's representable masks"
                ),
            ));
        }
        if v >= n_vertices {
            return Err(refuse(
                name,
                2,
                format!(
                    "`{what}` row cites vertex {v}, at or past the complex's {n_vertices} \
                     vertices — outside the spec model's representable masks"
                ),
            ));
        }
        target.entry(cell).or_default().insert(v);
    }
    Ok((simp, ext))
}

/// One strict λ-atom: `FAtom{LT|GT}(TAdd(TConst(off), TMul(TConst(slp),
/// TVar(input))), TConst(0))` — the RAW `baryLambdas1D` rendering
/// (constant on the left of the sum, no rescale, no zero-offset
/// special case). Comparator: strict interior takes `LT` for extended
/// vertices and `GT` for core ones; the out-witness atom (`reversed`)
/// takes the opposite pair.
fn lambda_atom(
    w: &mut Walk<'_>,
    atom: u32,
    coeff: &BaryCoeff,
    extended: bool,
    reversed: bool,
    input_wire: &Value,
) -> Result<bool, EvalError> {
    let expected = if extended != reversed {
        ATOM_LT
    } else {
        ATOM_GT
    };
    let (k, row) = w.form_ctor_row(1, atom)?;
    if k != FormCtor::Atom(expected) {
        return Ok(false);
    }
    // Right arm: the canonical rational zero.
    let r = w.local(1, &row.args[1])?;
    let (rk, r_row) = w.term_ctor_row(1, r)?;
    if rk != TermCtor::Const || !w.const_value(1, r_row)?.is_zero() {
        return Ok(false);
    }
    // Left arm: TAdd(TConst(off), TMul(TConst(slp), TVar(input))).
    let l = w.local(1, &row.args[0])?;
    let (lk, l_row) = w.term_ctor_row(1, l)?;
    if lk != TermCtor::Add {
        return Ok(false);
    }
    let off_elem = w.local(1, &l_row.args[0])?;
    let (ok, off_row) = w.term_ctor_row(1, off_elem)?;
    if ok != TermCtor::Const || w.const_value(1, off_row)? != coeff.off {
        return Ok(false);
    }
    let mul_elem = w.local(1, &l_row.args[1])?;
    let (mk, mul_row) = w.term_ctor_row(1, mul_elem)?;
    if mk != TermCtor::Mul {
        return Ok(false);
    }
    let slp_elem = w.local(1, &mul_row.args[0])?;
    let (sk, slp_row) = w.term_ctor_row(1, slp_elem)?;
    if sk != TermCtor::Const || w.const_value(1, slp_row)? != coeff.slp {
        return Ok(false);
    }
    let var_elem = w.local(1, &mul_row.args[1])?;
    let (vk, var_row) = w.term_ctor_row(1, var_elem)?;
    if vk != TermCtor::Var {
        return Ok(false);
    }
    w.nominal_eq(1, &var_row.args[0], input_wire)
}

/// One indicator atom: `FAtomEQ(TVar(wire), TConst(1|0))`, the wire
/// compared nominally.
fn indicator_atom(w: &mut Walk<'_>, atom: u32, wire: &Value, one: bool) -> Result<bool, EvalError> {
    let (k, row) = w.form_ctor_row(1, atom)?;
    if k != FormCtor::Atom(ATOM_EQ) {
        return Ok(false);
    }
    let l = w.local(1, &row.args[0])?;
    let (lk, l_row) = w.term_ctor_row(1, l)?;
    if lk != TermCtor::Var || !w.nominal_eq(1, &l_row.args[0], wire)? {
        return Ok(false);
    }
    let r = w.local(1, &row.args[1])?;
    let (rk, r_row) = w.term_ctor_row(1, r)?;
    if rk != TermCtor::Const {
        return Ok(false);
    }
    let expected = if one { QQ::one() } else { QQ::zero() };
    Ok(w.const_value(1, r_row)? == expected)
}

/// The four cell-schema forms, behind the shared destructure and
/// arity/range gate (module docs).
fn eval_cell_form(
    name: &str,
    blv: &BlVocab,
    bv: &BaryVocab,
    cav: &CellAppVocab,
    kind: ConclFormKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, blv, rows);
    // Field order: app, formula, schema, which[I|J] (, witnessVertex).
    let app = w.local(0, args[0])?;
    let formula = w.local(1, args[1])?;
    let schema = w.local(2, args[2])?;
    let which = nat_arg(name, 3, args[3])?;
    let witness = if kind == ConclFormKind::CellOutWitness {
        Some(nat_arg(name, 4, args[4])?)
    } else {
        None
    };

    let (input_wire, outputs) = destructure_cell_app(name, rows, cav, app)?;

    // The shared arity/range gate — REJECT is a decided false (module
    // docs: the build's `none` reading).
    let n_cells = unique_nat_field(name, 2, rows, schema, cav.simpc_n_cells, "SimpC/nCells")?;
    if which >= n_cells || outputs.len() as u64 != n_cells {
        return Ok(false);
    }

    match kind {
        ConclFormKind::CellOneHot => {
            // formula = FAnd(b_which = 1, chainAnd(b_j = 0, j ≠ which,
            // ascending)) — chainAnd: [] → FTrue, [f] → f, cons → FAnd.
            let (head, head_row) = w.form_ctor_row(1, formula)?;
            if head != FormCtor::And {
                return Ok(false);
            }
            let bk = w.local(1, &head_row.args[0])?;
            if !indicator_atom(&mut w, bk, &outputs[which as usize], true)? {
                return Ok(false);
            }
            let mut cur = w.local(1, &head_row.args[1])?;
            let others: Vec<&Value> = outputs
                .iter()
                .enumerate()
                .filter(|(j, _)| *j as u64 != which)
                .map(|(_, v)| v)
                .collect();
            let Some((last, init)) = others.split_last() else {
                // A single-cell schema: the second arm is FTrue.
                let (k, _) = w.form_ctor_row(1, cur)?;
                return Ok(k == FormCtor::True);
            };
            for other in init {
                let (k, row) = w.form_ctor_row(1, cur)?;
                if k != FormCtor::And {
                    return Ok(false);
                }
                let left = w.local(1, &row.args[0])?;
                if !indicator_atom(&mut w, left, other, false)? {
                    return Ok(false);
                }
                cur = w.local(1, &row.args[1])?;
            }
            indicator_atom(&mut w, cur, last, false)
        }
        ConclFormKind::CellOutZero => {
            // formula = the single atom (b_which = 0).
            indicator_atom(&mut w, formula, &outputs[which as usize], false)
        }
        ConclFormKind::CellStrictInterior | ConclFormKind::CellOutWitness => {
            let n = unique_nat_field(
                name,
                2,
                rows,
                schema,
                bv.simpc_n_vertices,
                "SimpC/n_vertices",
            )?;
            let amb = unique_nat_field(name, 2, rows, schema, bv.simpc_amb_dim, "SimpC/amb_dim")?;
            let (simp_masks, ext_masks) = cell_masks(name, rows, cav, schema, n_cells, n)?;
            let empty = BTreeSet::new();
            let smask = simp_masks.get(&which).unwrap_or(&empty);
            let emask = ext_masks.get(&which).unwrap_or(&empty);
            if let Some(wv) = witness {
                // The build's own guard: the witness vertex must belong
                // to the cell's simplex mask — decided false otherwise
                // (an out-of-range witnessVertex is subsumed: the mask's
                // rows are bounded, so it cannot be a member).
                if !smask.contains(&wv) {
                    return Ok(false);
                }
            }
            let Some(coeffs) = bary_coeffs_for_mask(name, 2, rows, bv, schema, n, amb, smask)?
            else {
                // The construction's `none` branches (ambient dimension
                // ≠ 1, mask size ≠ 2, coincident coordinates): decided
                // false for every formula argument.
                return Ok(false);
            };
            match kind {
                ConclFormKind::CellStrictInterior => {
                    // formula = FAnd(atom_a, atom_b), increasing vertex
                    // order.
                    let (head, head_row) = w.form_ctor_row(1, formula)?;
                    if head != FormCtor::And {
                        return Ok(false);
                    }
                    let arm0 = w.local(1, &head_row.args[0])?;
                    let arm1 = w.local(1, &head_row.args[1])?;
                    for (arm, coeff) in [(arm0, &coeffs[0]), (arm1, &coeffs[1])] {
                        let extended = emask.contains(&coeff.vertex);
                        if !lambda_atom(&mut w, arm, coeff, extended, false, &input_wire)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                ConclFormKind::CellOutWitness => {
                    let wv = witness.expect("witness decoded for this kind");
                    let coeff = coeffs
                        .iter()
                        .find(|c| c.vertex == wv)
                        .expect("the witness is a member of a two-vertex mask");
                    let extended = emask.contains(&wv);
                    lambda_atom(&mut w, formula, coeff, extended, true, &input_wire)
                }
                _ => unreachable!("outer match arm"),
            }
        }
        ConclFormKind::BarycentricHalfspace | ConclFormKind::Lirpa => {
            unreachable!("dispatched before the cell-form path")
        }
    }
}

// ---------------------------------------------------------------------
// The LiRPA conclusion form
// ---------------------------------------------------------------------

/// A `Q` literal argument cell (the `alpha`/`beta`/`gamma`/`delta`
/// fields), decoded to the exact canonical rational.
pub(crate) fn q_arg(name: &str, index: usize, v: &Value) -> Result<QQ, EvalError> {
    let Value::Lit(l) = v else {
        return Err(EvalError::ArgDtype {
            name: name.into(),
            index,
            expected: "Q",
            found: 0xFF,
        });
    };
    QQ::from_q_literal(l).ok_or_else(|| EvalError::ArgDtype {
        name: name.into(),
        index,
        expected: "Q",
        found: l.dtype_code(),
    })
}

/// A `Wire` argument cell: any element ref (local or external — wires
/// compare nominally, which normalizes both). A literal cell is
/// argument pathology, refused.
pub(crate) fn ref_arg<'v>(name: &str, index: usize, v: &'v Value) -> Result<&'v Value, EvalError> {
    if !matches!(v, Value::Ref(_)) {
        return Err(EvalError::ArgDtype {
            name: name.into(),
            index,
            expected: "element ref",
            found: 0xFF,
        });
    }
    Ok(v)
}

/// `TVar(wire)`, the wire compared nominally.
pub(crate) fn wire_var(
    w: &mut Walk<'_>,
    index: usize,
    elem: u32,
    wire: &Value,
) -> Result<bool, EvalError> {
    let (k, row) = w.term_ctor_row(index, elem)?;
    if k != TermCtor::Var {
        return Ok(false);
    }
    w.nominal_eq(index, &row.args[0], wire)
}

/// `TAdd(TConst(offset), TMul(TConst(slope), TVar(wire)))` — the Lean
/// `affineWireTerm offset slope wire` layout: offset FIRST in the sum,
/// constants on the LEFT, no zero special cases.
pub(crate) fn affine_wire_term(
    w: &mut Walk<'_>,
    index: usize,
    elem: u32,
    offset: &QQ,
    slope: &QQ,
    wire: &Value,
) -> Result<bool, EvalError> {
    let (k, row) = w.term_ctor_row(index, elem)?;
    if k != TermCtor::Add {
        return Ok(false);
    }
    let off_elem = w.local(index, &row.args[0])?;
    let (ok, off_row) = w.term_ctor_row(index, off_elem)?;
    if ok != TermCtor::Const || w.const_value(index, off_row)? != *offset {
        return Ok(false);
    }
    let mul_elem = w.local(index, &row.args[1])?;
    let (mk, mul_row) = w.term_ctor_row(index, mul_elem)?;
    if mk != TermCtor::Mul {
        return Ok(false);
    }
    let slp_elem = w.local(index, &mul_row.args[0])?;
    let (sk, slp_row) = w.term_ctor_row(index, slp_elem)?;
    if sk != TermCtor::Const || w.const_value(index, slp_row)? != *slope {
        return Ok(false);
    }
    let var_elem = w.local(index, &mul_row.args[1])?;
    wire_var(w, index, var_elem, wire)
}

/// `lirpaConclusionForm` — module docs. Equality with the Lean build,
/// decided by structural descent of the formula rows against the
/// fully-determined expected shape:
///
/// ```text
/// FAnd(FAtomLE(affineWireTerm(β, α, preact), TVar(post)),
///      FAtomLE(TVar(post), affineWireTerm(δ, γ, preact)))
/// ```
fn eval_lirpa(
    name: &str,
    blv: &BlVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, blv, rows);
    // Field order (registry bytewise): alpha, beta, delta, formula,
    // gamma, post, preact.
    let alpha = q_arg(name, 0, args[0])?;
    let beta = q_arg(name, 1, args[1])?;
    let delta = q_arg(name, 2, args[2])?;
    let formula = w.local(3, args[3])?;
    let gamma = q_arg(name, 4, args[4])?;
    let post = ref_arg(name, 5, args[5])?;
    let preact = ref_arg(name, 6, args[6])?;

    // formula = FAnd(lower, upper).
    let (head, head_row) = w.form_ctor_row(3, formula)?;
    if head != FormCtor::And {
        return Ok(false);
    }
    let lower = w.local(3, &head_row.args[0])?;
    let upper = w.local(3, &head_row.args[1])?;

    // lower = FAtomLE(affineWireTerm(β, α, preact), TVar(post)).
    let (lk, l_row) = w.form_ctor_row(3, lower)?;
    if lk != FormCtor::Atom(ATOM_LE) {
        return Ok(false);
    }
    let l_lhs = w.local(3, &l_row.args[0])?;
    if !affine_wire_term(&mut w, 3, l_lhs, &beta, &alpha, preact)? {
        return Ok(false);
    }
    let l_rhs = w.local(3, &l_row.args[1])?;
    if !wire_var(&mut w, 3, l_rhs, post)? {
        return Ok(false);
    }

    // upper = FAtomLE(TVar(post), affineWireTerm(δ, γ, preact)).
    let (uk, u_row) = w.form_ctor_row(3, upper)?;
    if uk != FormCtor::Atom(ATOM_LE) {
        return Ok(false);
    }
    let u_lhs = w.local(3, &u_row.args[0])?;
    if !wire_var(&mut w, 3, u_lhs, post)? {
        return Ok(false);
    }
    let u_rhs = w.local(3, &u_row.args[1])?;
    affine_wire_term(&mut w, 3, u_rhs, &delta, &gamma, preact)
}
