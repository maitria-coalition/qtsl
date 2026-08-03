//! The NN conclusion-form oracle family: the nine
//! ReLU/LiRPA premise- and conclusion-shape relations —
//! `reluPremNonnegForm`, `reluPremNonposForm`, `reluOutEqInputForm`,
//! `reluOutZeroForm`, `reluOutNonnegForm`, `reluOutDominatesForm`,
//! `lirpaPremLoForm`, `lirpaPremHiForm`, `lirpaSandwichForm`.
//!
//! Semantic authority: the Lean catalogue's rule-data types
//! (`lean/qtsl/Qtsl/Core/Catalogue.lean` — `PReLUPosData`,
//! `PReLUNegData`, `PReLUNNData`, `PReLUAboveData`, `PLiRPAData`),
//! whose premise/conclusion equalities pin every shape this family
//! checks:
//!
//! ```text
//!   reluPremNonnegForm   .atom .ge (.var h) (.const 0)
//!   reluPremNonposForm   .atom .le (.var h) (.const 0)
//!   reluOutEqInputForm   .atom .eq (.var y) (.var h)
//!   reluOutZeroForm      .atom .eq (.var y) (.const 0)
//!   reluOutNonnegForm    .atom .ge (.var y) (.const 0)
//!   reluOutDominatesForm .atom .ge (.var y) (.var h)
//!   lirpaPremLoForm      .atom .le (.const a) (.var h)     [a pinned]
//!   lirpaPremHiForm      .atom .le (.var h) (.const b)     [b pinned]
//!   lirpaSandwichForm    lirpaConclusionForm h y α β γ δ   [all pinned]
//! ```
//!
//! where `h`/`y` are the cited PReLU application's position-0 input
//! and output wires (the theory's linkage reading: "key-identified
//! port lookups, destructured by the conclusion-form relations exactly
//! as the cell forms destructure the cell application"). The sandwich
//! shape is the SAME build as `lirpaConclusionForm` and the walk
//! reuses [`crate::blconclform`]'s `affine_wire_term`/`wire_var` —
//! one rendering, one implementation (two implementations of
//! "canonical" is the divergence hazard the word exists to exclude).
//!
//! # The app destructure (the theory's REJECT reading)
//!
//! The design source's declaration comment: each relation
//! "destructures the ReLU application's position-0 ports and REJECTS
//! unless the app is a PReLU application with both ports present".
//! REJECT is a decided `false`:
//!
//! - `PrimApp/prim` resolving to a constructor other than `PReLU` —
//!   not a ReLU application;
//! - either position-0 port ABSENT — "both ports present" fails.
//!
//! Refusal classes, deliberately NOT decided verdicts (the crate's
//! walk discipline — never guess): an app argument that is not a
//! same-body element ref; a missing or ambiguous `PrimApp/prim` row
//! (what primitive an app is cannot be guessed from silence); a prim
//! value or port element that is an external ref; conflicting port
//! wires at position 0 (the port-uniqueness axiom admits no such
//! state); non-`Q` pinned-rational cells; and the usual row pathology
//! under the formula walk. Ports at positions other than 0 are
//! IGNORED (key-identified lookup — arity conformance is other rows'
//! business, unlike the cell forms' dense-arity read).
//!
//! Wires compare NOMINALLY (local or external element refs — the cell
//! forms' normalization); the pinned rationals compare as exact
//! canonical `Q`; everything below the formula head decides `false`
//! on mismatch.

use crate::blconclform::{affine_wire_term, q_arg, wire_var, ATOM_EQ, ATOM_GE, ATOM_LE};
use crate::error::EvalError;
use crate::formrows::{BlVocab, FormCtor, TermCtor, Walk};
use crate::qq::QQ;
use crate::roster::{EntryRow, NnFormKind, RelKind};
use crate::rowctx::CertRows;
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::Value;

const F_RELU: &[(&str, &str)] = &[("app", "PrimApp"), ("formula", "Formula")];
const F_PREM_LO: &[(&str, &str)] = &[("a", "Q"), ("app", "PrimApp"), ("formula", "Formula")];
const F_PREM_HI: &[(&str, &str)] = &[("app", "PrimApp"), ("b", "Q"), ("formula", "Formula")];
const F_SANDWICH: &[(&str, &str)] = &[
    ("alpha", "Q"),
    ("app", "PrimApp"),
    ("beta", "Q"),
    ("delta", "Q"),
    ("formula", "Formula"),
    ("gamma", "Q"),
];

/// The NN conclusion-form family's rows of the claimed roster,
/// theory declaration order. Appended as its own table at the END of
/// the provider's family list (existing roster positions are
/// provider-local indices — unchanged by construction).
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "reluPremNonnegForm",
        F_RELU,
        RelKind::NnForm(NnFormKind::ReluPremNonneg),
    ),
    (
        "reluPremNonposForm",
        F_RELU,
        RelKind::NnForm(NnFormKind::ReluPremNonpos),
    ),
    (
        "reluOutEqInputForm",
        F_RELU,
        RelKind::NnForm(NnFormKind::ReluOutEqInput),
    ),
    (
        "reluOutZeroForm",
        F_RELU,
        RelKind::NnForm(NnFormKind::ReluOutZero),
    ),
    (
        "reluOutNonnegForm",
        F_RELU,
        RelKind::NnForm(NnFormKind::ReluOutNonneg),
    ),
    (
        "reluOutDominatesForm",
        F_RELU,
        RelKind::NnForm(NnFormKind::ReluOutDominates),
    ),
    (
        "lirpaPremLoForm",
        F_PREM_LO,
        RelKind::NnForm(NnFormKind::LirpaPremLo),
    ),
    (
        "lirpaPremHiForm",
        F_PREM_HI,
        RelKind::NnForm(NnFormKind::LirpaPremHi),
    ),
    (
        "lirpaSandwichForm",
        F_SANDWICH,
        RelKind::NnForm(NnFormKind::LirpaSandwich),
    ),
];

/// The ReLU-application vocabulary: the hypernet port fields, the
/// primitive tag field, and the `PReLU` constructor. Deliberately NOT
/// [`crate::blconclform::CellAppVocab`]: that group additionally
/// requires the certificate EXTENSION's `SimpC/nCells`, which the
/// baked closures do not carry — this family must claim there, so it
/// resolves its own strictly-smaller name set.
#[derive(Debug, Clone)]
pub struct NnFormVocab {
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
    /// `PrimApp/prim : PrimApp -> Primitive`.
    pub(crate) primapp_prim: Chid,
    /// `PReLU : Primitive` (nullary constructor).
    pub(crate) prelu: Chid,
}

/// Build the ReLU-application vocabulary over the declared indices.
/// `Err` → the family is not claimed (declared-but-unbound,
/// safe-fail).
pub fn build_nnform_vocab(
    indices: &[&TheoryIndex],
    input_port_sort: Chid,
    output_port_sort: Chid,
    primapp_sort: Chid,
    wire_sort: Chid,
    primitive_sort: Chid,
) -> Result<NnFormVocab, String> {
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
    let constant = |name: &str, cod: Chid| -> Result<Chid, String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            let shape_ok = !d.relational
                && d.codomain == Some(SortKey::Elem(cod))
                && d.domain == DomainSig::Nullary;
            if !shape_ok {
                return Err(format!(
                    "`{name}` does not have the expected nullary-constant shape"
                ));
            }
            return Ok(d.chid);
        }
        Err(format!("no `{name}` declaration among the swept revisions"))
    };
    Ok(NnFormVocab {
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
        primapp_prim: field("PrimApp/prim", primapp_sort, SortKey::Elem(primitive_sort))?,
        prelu: constant("PReLU", primitive_sort)?,
    })
}

fn refuse(name: &str, index: usize, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.into(),
        index,
        why,
    }
}

/// The sole nullary-constructor row producing `elem`, its fun
/// returned to COMPARE (not a classified kind): an app primed by some
/// other constant is a decided `false` at the caller, which a
/// roster-filtered lookup would misreport as unresolvable. The
/// producers index is value-keyed, so it also carries FIELD rows whose
/// value is this element (`PrimApp/prim` itself, from the app's side)
/// — a constant's own constructor row is the one with NO arguments,
/// and that shape is the filter.
pub(crate) fn sole_nullary_ctor_fun(
    name: &str,
    index: usize,
    rows: &CertRows,
    elem: u32,
    what: &str,
) -> Result<Chid, EvalError> {
    let mut found: Option<Chid> = None;
    for row in rows.producers(elem) {
        if !row.args.is_empty() {
            continue; // a field/attribute row citing the element, not its constructor
        }
        if found.is_some() {
            return Err(refuse(
                name,
                index,
                format!(
                    "{what} element {elem} is produced by multiple constructor rows — \
                     ambiguous structure (P-FUN territory), refusing"
                ),
            ));
        }
        found = Some(row.fun);
    }
    found.ok_or_else(|| {
        refuse(
            name,
            index,
            format!(
                "{what} element {elem} has no constructor row in the context — \
                 structure undecidable"
            ),
        )
    })
}

/// One side's position-0 port wire, key-identified: scan the app's
/// citing port rows, keep only position 0, refuse on conflicting
/// wires there, ignore every other position. `Ok(None)` = no
/// position-0 port in view (the caller's decided `false`).
#[allow(clippy::too_many_arguments)]
fn position0_wire(
    name: &str,
    rows: &CertRows,
    app: u32,
    app_fun: Chid,
    pos_fun: Chid,
    wire_fun: Chid,
    side: &str,
) -> Result<Option<Value>, EvalError> {
    let mut found: Option<Value> = None;
    for row in rows.producers(app) {
        if row.fun != app_fun {
            continue;
        }
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
        let pos = crate::barycoord::unique_nat_field(
            name,
            0,
            rows,
            port,
            pos_fun,
            &format!("{side}/pos"),
        )?;
        if pos != 0 {
            continue; // key-identified lookup: other positions are not in view
        }
        let wire = unique_ref_field_value(name, rows, port, wire_fun, &format!("{side}/wire"))?;
        match &found {
            None => found = Some(wire),
            Some(prev) if *prev == wire => {}
            Some(_) => {
                return Err(refuse(
                    name,
                    0,
                    format!(
                        "conflicting `{side}` wires at position 0 — the port-uniqueness \
                         axiom admits no such state; never picking"
                    ),
                ))
            }
        }
    }
    Ok(found)
}

/// The unique field row's value on `subject`, required to be an
/// element ref (local or external — wires compare nominally). Zero
/// rows refuse, conflicting values refuse.
fn unique_ref_field_value(
    name: &str,
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
                0,
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
                    0,
                    format!("ambiguous `{what}`: conflicting field rows — never picking"),
                ))
            }
        }
    }
    let Some(value) = found else {
        return Err(refuse(
            name,
            0,
            format!("no `{what}` row for the element in view — unresolvable"),
        ));
    };
    if !matches!(value, Value::Ref(_)) {
        return Err(refuse(
            name,
            0,
            format!("malformed `{what}` row: value is not an element ref"),
        ));
    }
    Ok(value.clone())
}

/// Destructure the ReLU application: `Ok(None)` is the REJECT reading
/// (not a PReLU application, or a position-0 port absent) — a decided
/// `false` at the caller; `Ok(Some((h, y)))` carries the position-0
/// input and output wires.
fn destructure_relu_app(
    name: &str,
    v: &NnFormVocab,
    rows: &CertRows,
    app_index: usize,
    app_val: &Value,
) -> Result<Option<(Value, Value)>, EvalError> {
    // The app: a same-body element (the port and prim reads are
    // single-body walks, exactly as the cell forms').
    let app = match app_val {
        Value::Ref(r) => rows.local(r).ok_or_else(|| {
            refuse(
                name,
                app_index,
                "the app argument cites an external element — single-body context".into(),
            )
        })?,
        _ => {
            return Err(EvalError::ArgDtype {
                name: name.into(),
                index: app_index,
                expected: "element ref",
                found: 0xFF,
            })
        }
    };

    // The primitive tag: `PrimApp/prim = PReLU`, or REJECT. A missing
    // or ambiguous prim row refuses (what primitive an app is cannot
    // be guessed from silence); a prim value produced by any OTHER
    // constructor is a decided `false`.
    let prim_val = unique_ref_field_value(name, rows, app, v.primapp_prim, "PrimApp/prim")?;
    let prim_elem = match &prim_val {
        Value::Ref(r) => rows.local(r).ok_or_else(|| {
            refuse(
                name,
                app_index,
                "`PrimApp/prim` cites an external element — single-body context".into(),
            )
        })?,
        _ => unreachable!("unique_ref_field_value returns element refs"),
    };
    if sole_nullary_ctor_fun(name, app_index, rows, prim_elem, "`PrimApp/prim` value")? != v.prelu {
        return Ok(None); // not a PReLU application — REJECT
    }

    // The position-0 ports, key-identified; either absent → REJECT.
    let h = position0_wire(
        name,
        rows,
        app,
        v.input_app,
        v.input_pos,
        v.input_wire,
        "InputPort",
    )?;
    let y = position0_wire(
        name,
        rows,
        app,
        v.output_app,
        v.output_pos,
        v.output_wire,
        "OutputPort",
    )?;
    match (h, y) {
        (Some(h), Some(y)) => Ok(Some((h, y))),
        _ => Ok(None), // "both ports present" fails — REJECT
    }
}

/// One bare atom `FAtom<code>(lhs, rhs)` where each side is either
/// `TVar(wire)` or `TConst(q)` — the Lean rule-data premise/conclusion
/// shapes, which carry no compound terms.
enum Side<'a> {
    Var(&'a Value),
    Const(&'a QQ),
}

fn side_matches(
    w: &mut Walk<'_>,
    index: usize,
    elem: u32,
    side: &Side<'_>,
) -> Result<bool, EvalError> {
    match side {
        Side::Var(wire) => wire_var(w, index, elem, wire),
        Side::Const(q) => {
            let (k, row) = w.term_ctor_row(index, elem)?;
            if k != TermCtor::Const {
                return Ok(false);
            }
            Ok(w.const_value(index, row)? == **q)
        }
    }
}

fn bare_atom(
    w: &mut Walk<'_>,
    index: usize,
    formula: u32,
    code: u8,
    lhs: &Side<'_>,
    rhs: &Side<'_>,
) -> Result<bool, EvalError> {
    let (head, row) = w.form_ctor_row(index, formula)?;
    if head != FormCtor::Atom(code) {
        return Ok(false);
    }
    let l = w.local(index, &row.args[0])?;
    if !side_matches(w, index, l, lhs)? {
        return Ok(false);
    }
    let r = w.local(index, &row.args[1])?;
    side_matches(w, index, r, rhs)
}

/// Evaluate an NN conclusion-form relation. Argument cells arrive in
/// declared (bytewise) field order — the entry table above.
pub(crate) fn eval_nnform(
    name: &str,
    blv: &BlVocab,
    v: &NnFormVocab,
    kind: NnFormKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    // Field positions per signature (bytewise order).
    // F_RELU: app, formula. F_PREM_LO: a, app, formula.
    // F_PREM_HI: app, b, formula.
    // F_SANDWICH: alpha, app, beta, delta, formula, gamma.
    let zero = QQ::zero();
    let mut w = Walk::new(name, blv, rows);
    match kind {
        NnFormKind::ReluPremNonneg
        | NnFormKind::ReluPremNonpos
        | NnFormKind::ReluOutEqInput
        | NnFormKind::ReluOutZero
        | NnFormKind::ReluOutNonneg
        | NnFormKind::ReluOutDominates => {
            let Some((h, y)) = destructure_relu_app(name, v, rows, 0, args[0])? else {
                return Ok(false);
            };
            let formula = w.local(1, args[1])?;
            let (code, lhs, rhs) = match kind {
                // .atom .ge (.var preact) (.const 0)
                NnFormKind::ReluPremNonneg => (ATOM_GE, Side::Var(&h), Side::Const(&zero)),
                // .atom .le (.var preact) (.const 0)
                NnFormKind::ReluPremNonpos => (ATOM_LE, Side::Var(&h), Side::Const(&zero)),
                // .atom .eq (.var post) (.var preact)
                NnFormKind::ReluOutEqInput => (ATOM_EQ, Side::Var(&y), Side::Var(&h)),
                // .atom .eq (.var post) (.const 0)
                NnFormKind::ReluOutZero => (ATOM_EQ, Side::Var(&y), Side::Const(&zero)),
                // .atom .ge (.var post) (.const 0)
                NnFormKind::ReluOutNonneg => (ATOM_GE, Side::Var(&y), Side::Const(&zero)),
                // .atom .ge (.var post) (.var preact)
                NnFormKind::ReluOutDominates => (ATOM_GE, Side::Var(&y), Side::Var(&h)),
                _ => unreachable!("outer match arm"),
            };
            bare_atom(&mut w, 1, formula, code, &lhs, &rhs)
        }
        NnFormKind::LirpaPremLo => {
            // Fields: a, app, formula.
            let a = q_arg(name, 0, args[0])?;
            let Some((h, _y)) = destructure_relu_app(name, v, rows, 1, args[1])? else {
                return Ok(false);
            };
            let formula = w.local(2, args[2])?;
            // .atom .le (.const a) (.var preact)
            bare_atom(
                &mut w,
                2,
                formula,
                ATOM_LE,
                &Side::Const(&a),
                &Side::Var(&h),
            )
        }
        NnFormKind::LirpaPremHi => {
            // Fields: app, b, formula.
            let b = q_arg(name, 1, args[1])?;
            let Some((h, _y)) = destructure_relu_app(name, v, rows, 0, args[0])? else {
                return Ok(false);
            };
            let formula = w.local(2, args[2])?;
            // .atom .le (.var preact) (.const b)
            bare_atom(
                &mut w,
                2,
                formula,
                ATOM_LE,
                &Side::Var(&h),
                &Side::Const(&b),
            )
        }
        NnFormKind::LirpaSandwich => {
            // Fields: alpha, app, beta, delta, formula, gamma.
            let alpha = q_arg(name, 0, args[0])?;
            let beta = q_arg(name, 2, args[2])?;
            let delta = q_arg(name, 3, args[3])?;
            let gamma = q_arg(name, 5, args[5])?;
            let Some((h, y)) = destructure_relu_app(name, v, rows, 1, args[1])? else {
                return Ok(false);
            };
            let formula = w.local(4, args[4])?;

            // The lirpaConclusionForm build over the app's own ports:
            // FAnd(FAtomLE(affine(β, α, h), TVar(y)),
            //      FAtomLE(TVar(y), affine(δ, γ, h))).
            let (head, head_row) = w.form_ctor_row(4, formula)?;
            if head != FormCtor::And {
                return Ok(false);
            }
            let lower = w.local(4, &head_row.args[0])?;
            let upper = w.local(4, &head_row.args[1])?;

            let (lk, l_row) = w.form_ctor_row(4, lower)?;
            if lk != FormCtor::Atom(ATOM_LE) {
                return Ok(false);
            }
            let l_lhs = w.local(4, &l_row.args[0])?;
            if !affine_wire_term(&mut w, 4, l_lhs, &beta, &alpha, &h)? {
                return Ok(false);
            }
            let l_rhs = w.local(4, &l_row.args[1])?;
            if !wire_var(&mut w, 4, l_rhs, &y)? {
                return Ok(false);
            }

            let (uk, u_row) = w.form_ctor_row(4, upper)?;
            if uk != FormCtor::Atom(ATOM_LE) {
                return Ok(false);
            }
            let u_lhs = w.local(4, &u_row.args[0])?;
            if !wire_var(&mut w, 4, u_lhs, &y)? {
                return Ok(false);
            }
            let u_rhs = w.local(4, &u_row.args[1])?;
            affine_wire_term(&mut w, 4, u_rhs, &delta, &gamma, &h)
        }
    }
}
