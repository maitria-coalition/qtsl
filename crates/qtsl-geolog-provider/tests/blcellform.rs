//! The four cell-schema conclusion forms exercised end to end through
//! provider dispatch: `cellStrictInteriorForm`, `cellOneHotForm`,
//! `cellOutWitnessForm`, `cellOutZeroForm` — expected formulas
//! recomputed from schema geometry + cell-mask + port rows and
//! compared structurally against formula rows. Spec battery (golden
//! anchors hand-derived from the Lean builds over the executable
//! demo's geometry), named data mutants (every mutant flips a
//! verdict), the shared arity/range gate, decided-`false` shapes,
//! refusals, and the frozen cross-implementation corpus.
//!
//! The test-side row emitter shares no code with the evaluators: it
//! writes `Op::Funa` constructor/field rows and `Op::Rela` mask rows
//! directly from the synthetic declaration index.

mod common;

use common::{provider, stack, STACK};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;

const OWN: [u8; 32] = [0xCE; 32];

fn s_fun(name: &str) -> Chid {
    stack()
        .fun(name)
        .unwrap_or_else(|| panic!("stack fun `{name}`"))
        .chid
}

fn lref(e: u32) -> Value {
    Value::Ref(ElemRef::Local(e))
}

fn natv(n: u64) -> Value {
    Value::Lit(Literal::nat(n))
}

fn qv(num: i64, den: u64) -> Value {
    Value::Lit(Literal::q(num, den).expect("canonical q"))
}

/// Geometry + hypernet + syntax bodies in miniature: complexes with
/// vertex tables and cell masks, cell applications with port rows,
/// and Term/Formula constructor rows.
struct Body {
    ops: Vec<Op>,
    next: u32,
    deps: Vec<[u8; 32]>,
}

impl Body {
    fn new() -> Body {
        Body {
            ops: Vec::new(),
            next: 0,
            deps: vec![STACK],
        }
    }

    fn xref(&self, c: Chid) -> ElemRef {
        let dep_index = self
            .deps
            .iter()
            .position(|d| *d == c.0)
            .expect("chid homed in a dep") as u32;
        ElemRef::External {
            dep_index,
            counter: c.1,
        }
    }

    fn fresh(&mut self) -> u32 {
        let e = self.next;
        self.next += 1;
        e
    }

    fn field(&mut self, fun: &str, subject: u32, value: Value) {
        self.ops.push(Op::Funa {
            fun: self.xref(s_fun(fun)),
            args: vec![lref(subject)],
            value,
        });
    }

    /// A `SimpC/coord` row (field order bytewise: complex, j, v).
    fn coord(&mut self, complex: u32, v: u64, j: u64, num: i64, den: u64) {
        self.ops.push(Op::Funa {
            fun: self.xref(s_fun("SimpC/coord")),
            args: vec![lref(complex), natv(j), natv(v)],
            value: qv(num, den),
        });
    }

    /// A cell-mask row (field order bytewise: cell, complex, v).
    fn mask_row(&mut self, rel: &str, complex: u32, cell: u64, v: u64) {
        self.ops.push(Op::Rela {
            rel: self.xref(s_fun(rel)),
            args: vec![natv(cell), lref(complex), natv(v)],
        });
    }

    /// A complex with `n` vertices in a line (`amb_dim = 1`) and the
    /// given cells, each `(simplex mask, extension mask)`.
    fn schema(&mut self, coords: &[(i64, u64)], cells: &[(&[u64], &[u64])]) -> u32 {
        let c = self.fresh();
        self.field("SimpC/n_vertices", c, natv(coords.len() as u64));
        self.field("SimpC/amb_dim", c, natv(1));
        for (v, (num, den)) in coords.iter().enumerate() {
            self.coord(c, v as u64, 0, *num, *den);
        }
        self.field("SimpC/nCells", c, natv(cells.len() as u64));
        for (k, (simplex, ext)) in cells.iter().enumerate() {
            for &v in *simplex {
                self.mask_row("CellSimplexHasV", c, k as u64, v);
            }
            for &v in *ext {
                self.mask_row("CellExtHasV", c, k as u64, v);
            }
        }
        c
    }

    /// A cell application: one input port at position 0 carrying
    /// `input`, and one output port per entry of `outputs`, at
    /// positions 0..m-1. Returns the app element.
    fn app(&mut self, input: u32, outputs: &[u32]) -> u32 {
        let app = self.fresh();
        let p = self.fresh();
        self.field("InputPort/app", p, lref(app));
        self.field("InputPort/pos", p, natv(0));
        self.field("InputPort/wire", p, lref(input));
        for (i, &w) in outputs.iter().enumerate() {
            let q = self.fresh();
            self.field("OutputPort/app", q, lref(app));
            self.field("OutputPort/pos", q, natv(i as u64));
            self.field("OutputPort/wire", q, lref(w));
        }
        app
    }

    // ---- Term/Formula constructor rows -----------------------------

    fn ctor(&mut self, fun: &str, args: Vec<Value>) -> u32 {
        let e = self.fresh();
        self.ops.push(Op::Funa {
            fun: self.xref(s_fun(fun)),
            args,
            value: lref(e),
        });
        e
    }

    fn tvar(&mut self, wire: u32) -> u32 {
        self.ctor("TVar", vec![lref(wire)])
    }

    fn tconst(&mut self, num: i64, den: u64) -> u32 {
        self.ctor("TConst", vec![qv(num, den)])
    }

    fn tadd(&mut self, l: u32, r: u32) -> u32 {
        self.ctor("TAdd", vec![lref(l), lref(r)])
    }

    fn tmul(&mut self, l: u32, r: u32) -> u32 {
        self.ctor("TMul", vec![lref(l), lref(r)])
    }

    fn fatom(&mut self, name: &str, l: u32, r: u32) -> u32 {
        self.ctor(name, vec![lref(l), lref(r)])
    }

    fn fand(&mut self, l: u32, r: u32) -> u32 {
        self.ctor("FAnd", vec![lref(l), lref(r)])
    }

    fn ftrue(&mut self) -> u32 {
        self.ctor("FTrue", vec![])
    }

    /// One strict λ-atom in the realized rendering:
    /// `FAtom{op}(TAdd(TConst(off), TMul(TConst(slp), TVar(wire))),
    /// TConst(0))` — constant on the LEFT of the sum, no rescale, no
    /// zero-offset special case.
    fn lam_atom(&mut self, op: &str, off: (i64, u64), slp: (i64, u64), wire: u32) -> u32 {
        let offc = self.tconst(off.0, off.1);
        let slpc = self.tconst(slp.0, slp.1);
        let v = self.tvar(wire);
        let prod = self.tmul(slpc, v);
        let lhs = self.tadd(offc, prod);
        let zero = self.tconst(0, 1);
        self.fatom(op, lhs, zero)
    }

    /// One indicator atom `FAtomEQ(TVar(wire), TConst(val))`.
    fn ind_atom(&mut self, wire: u32, val: i64) -> u32 {
        let v = self.tvar(wire);
        let c = self.tconst(val, 1);
        self.fatom("FAtomEQ", v, c)
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

// ---- dispatch helpers (declared bytewise field orders) ---------------

/// `cellStrictInteriorForm` / `cellOneHotForm`: app, formula, schema,
/// whichI.
fn ev4(
    name: &str,
    app: u32,
    formula: u32,
    schema: u32,
    which: u64,
    b: &Body,
) -> Result<bool, String> {
    let args = [lref(app), lref(formula), lref(schema), natv(which)];
    let refs: Vec<&Value> = args.iter().collect();
    common::ev(name, &refs, &b.rows())
}

/// `cellOutWitnessForm`: app, formula, schema, whichJ, witnessVertex.
fn ev5(
    app: u32,
    formula: u32,
    schema: u32,
    which: u64,
    witness: u64,
    b: &Body,
) -> Result<bool, String> {
    let args = [
        lref(app),
        lref(formula),
        lref(schema),
        natv(which),
        natv(witness),
    ];
    let refs: Vec<&Value> = args.iter().collect();
    common::ev("cellOutWitnessForm", &refs, &b.rows())
}

/// The Lean demo's geometry, one cell: vertices at 1 and 2, cell 0 =
/// ({0, 1}, ∅). λ₀ = 2 + (−1)·x, λ₁ = −1 + 1·x.
fn demo1(b: &mut Body) -> (u32, u32, u32, u32) {
    let schema = b.schema(&[(1, 1), (2, 1)], &[(&[0, 1], &[])]);
    let input = b.fresh();
    let b0 = b.fresh();
    let app = b.app(input, &[b0]);
    (schema, app, input, b0)
}

/// A two-cell schema: vertices at 0, 1, 2; cell 0 = ({0,1}, ∅),
/// cell 1 = ({1,2}, {2}). λ-pairs: cell 0 → (1, −1), (0, 1);
/// cell 1 → (2, −1), (−1, 1).
fn demo2(b: &mut Body) -> (u32, u32, u32, [u32; 2]) {
    let schema = b.schema(
        &[(0, 1), (1, 1), (2, 1)],
        &[(&[0, 1], &[]), (&[1, 2], &[2])],
    );
    let input = b.fresh();
    let b0 = b.fresh();
    let b1 = b.fresh();
    let app = b.app(input, &[b0, b1]);
    (schema, app, input, [b0, b1])
}

// ---------------------------------------------------------------------
// Golden anchors, hand-derived from the Lean builds (the executable
// demo's geometry; derivations in the atoms' comments).
// ---------------------------------------------------------------------

#[test]
fn strict_interior_demo_holds() {
    // Both vertices core: λ₀ > 0 AND λ₁ > 0, raw coefficients.
    let mut b = Body::new();
    let (schema, app, input, _b0) = demo1(&mut b);
    let a0 = b.lam_atom("FAtomGT", (2, 1), (-1, 1), input);
    let a1 = b.lam_atom("FAtomGT", (-1, 1), (1, 1), input);
    let f = b.fand(a0, a1);
    assert_eq!(
        ev4("cellStrictInteriorForm", app, f, schema, 0, &b),
        Ok(true)
    );
}

#[test]
fn strict_interior_extended_vertex_takes_lt() {
    // Cell 1 of demo2 extends through vertex 2: λ₁ > 0 AND λ₂ < 0.
    let mut b = Body::new();
    let (schema, app, input, _) = demo2(&mut b);
    let a0 = b.lam_atom("FAtomGT", (2, 1), (-1, 1), input);
    let a1 = b.lam_atom("FAtomLT", (-1, 1), (1, 1), input);
    let f = b.fand(a0, a1);
    assert_eq!(
        ev4("cellStrictInteriorForm", app, f, schema, 1, &b),
        Ok(true)
    );
}

#[test]
fn strict_interior_zero_offset_keeps_the_add_layout() {
    // Cell 0 of demo2: λ₁ = 0 + 1·x — the zero offset STAYS a
    // `TAdd(TConst(0), …)` (the raw `baryLambdas1D` rendering has no
    // bare-product special case, unlike the halfspace form's).
    let mut b = Body::new();
    let (schema, app, input, _) = demo2(&mut b);
    let a0 = b.lam_atom("FAtomGT", (1, 1), (-1, 1), input);
    let a1 = b.lam_atom("FAtomGT", (0, 1), (1, 1), input);
    let f = b.fand(a0, a1);
    assert_eq!(
        ev4("cellStrictInteriorForm", app, f, schema, 0, &b),
        Ok(true)
    );
}

#[test]
fn strict_interior_fractional_coefficients_stay_raw() {
    // Vertices at 1/2 and 3/2: den = 1, λ₀ = 3/2 + (−1)·x,
    // λ₁ = −1/2 + 1·x — fractional offsets, carried RAW.
    let mut b = Body::new();
    let schema = b.schema(&[(1, 2), (3, 2)], &[(&[0, 1], &[])]);
    let input = b.fresh();
    let b0 = b.fresh();
    let app = b.app(input, &[b0]);
    let a0 = b.lam_atom("FAtomGT", (3, 2), (-1, 1), input);
    let a1 = b.lam_atom("FAtomGT", (-1, 2), (1, 1), input);
    let f = b.fand(a0, a1);
    assert_eq!(
        ev4("cellStrictInteriorForm", app, f, schema, 0, &b),
        Ok(true)
    );
}

#[test]
fn one_hot_single_cell_is_bk_and_ftrue() {
    // A single-cell schema: (b₀ = 1) AND FTrue — chainAnd([]) = FTrue.
    let mut b = Body::new();
    let (schema, app, _input, b0) = demo1(&mut b);
    let bk = b.ind_atom(b0, 1);
    let tt = b.ftrue();
    let f = b.fand(bk, tt);
    assert_eq!(ev4("cellOneHotForm", app, f, schema, 0, &b), Ok(true));
}

#[test]
fn one_hot_two_cells_second_arm_is_the_bare_atom() {
    // chainAnd([f]) = f: FAnd(b₁ = 1, b₀ = 0), no FTrue tail.
    let mut b = Body::new();
    let (schema, app, _input, outs) = demo2(&mut b);
    let bk = b.ind_atom(outs[1], 1);
    let other = b.ind_atom(outs[0], 0);
    let f = b.fand(bk, other);
    assert_eq!(ev4("cellOneHotForm", app, f, schema, 1, &b), Ok(true));
}

#[test]
fn one_hot_three_cells_nests_the_chain() {
    // whichI = 1 of three: FAnd(b₁ = 1, FAnd(b₀ = 0, b₂ = 0)) —
    // others ascending, cons-nested, no FTrue tail.
    let mut b = Body::new();
    let schema = b.schema(
        &[(0, 1), (1, 1), (2, 1), (3, 1)],
        &[(&[0, 1], &[]), (&[1, 2], &[]), (&[2, 3], &[])],
    );
    let input = b.fresh();
    let outs = [b.fresh(), b.fresh(), b.fresh()];
    let app = b.app(input, &outs);
    let bk = b.ind_atom(outs[1], 1);
    let o0 = b.ind_atom(outs[0], 0);
    let o2 = b.ind_atom(outs[2], 0);
    let tail = b.fand(o0, o2);
    let f = b.fand(bk, tail);
    assert_eq!(ev4("cellOneHotForm", app, f, schema, 1, &b), Ok(true));
}

#[test]
fn out_witness_core_vertex_takes_lt() {
    // Witness at core vertex 0 of demo1's cell: the single atom
    // λ₀ < 0 — REVERSED against the strict-interior sign.
    let mut b = Body::new();
    let (schema, app, input, _b0) = demo1(&mut b);
    let f = b.lam_atom("FAtomLT", (2, 1), (-1, 1), input);
    assert_eq!(ev5(app, f, schema, 0, 0, &b), Ok(true));
}

#[test]
fn out_witness_extended_vertex_takes_gt() {
    // Cell 1 of demo2 extends through vertex 2: witness there is
    // λ₂ > 0.
    let mut b = Body::new();
    let (schema, app, input, _) = demo2(&mut b);
    let f = b.lam_atom("FAtomGT", (-1, 1), (1, 1), input);
    assert_eq!(ev5(app, f, schema, 1, 2, &b), Ok(true));
}

#[test]
fn out_zero_demo_holds() {
    let mut b = Body::new();
    let (schema, app, _input, outs) = demo2(&mut b);
    let f = b.ind_atom(outs[1], 0);
    assert_eq!(ev4("cellOutZeroForm", app, f, schema, 1, &b), Ok(true));
}

#[test]
fn non_interned_copies_compare_structurally() {
    // The formula's TVar rows are fresh elements over the SAME wires —
    // structural comparison, nominal only at the wire positions.
    let mut b = Body::new();
    let (schema, app, input, _b0) = demo1(&mut b);
    let a0 = b.lam_atom("FAtomGT", (2, 1), (-1, 1), input);
    let a1 = b.lam_atom("FAtomGT", (-1, 1), (1, 1), input);
    let f = b.fand(a0, a1);
    // A second, disjoint rendering of the same formula shape.
    let a0b = b.lam_atom("FAtomGT", (2, 1), (-1, 1), input);
    let a1b = b.lam_atom("FAtomGT", (-1, 1), (1, 1), input);
    let f2 = b.fand(a0b, a1b);
    assert_ne!(f, f2);
    assert_eq!(
        ev4("cellStrictInteriorForm", app, f, schema, 0, &b),
        Ok(true)
    );
    assert_eq!(
        ev4("cellStrictInteriorForm", app, f2, schema, 0, &b),
        Ok(true)
    );
}

// ---------------------------------------------------------------------
// The shared arity/range gate: decided false, all four forms.
// ---------------------------------------------------------------------

#[test]
fn gate_out_of_range_index_fails_all_forms() {
    let mut b = Body::new();
    let (schema, app, input, outs) = demo2(&mut b);
    let a0 = b.lam_atom("FAtomGT", (1, 1), (-1, 1), input);
    let a1 = b.lam_atom("FAtomGT", (0, 1), (1, 1), input);
    let strict = b.fand(a0, a1);
    let bk = b.ind_atom(outs[0], 1);
    let other = b.ind_atom(outs[1], 0);
    let onehot = b.fand(bk, other);
    let witness = b.lam_atom("FAtomLT", (1, 1), (-1, 1), input);
    let zero = b.ind_atom(outs[0], 0);
    // whichI = 2 == nCells: out of range, decided false.
    assert_eq!(
        ev4("cellStrictInteriorForm", app, strict, schema, 2, &b),
        Ok(false)
    );
    assert_eq!(ev4("cellOneHotForm", app, onehot, schema, 2, &b), Ok(false));
    assert_eq!(ev5(app, witness, schema, 2, 0, &b), Ok(false));
    assert_eq!(ev4("cellOutZeroForm", app, zero, schema, 2, &b), Ok(false));
}

#[test]
fn gate_arity_mismatch_fails_all_forms() {
    // Three output ports against a two-cell schema: the output arity
    // gate decides false for every form — including the two whose
    // Lean Props never read the outputs (the frozen spec's uniform
    // gate is exactly the extra strictness under test here).
    let mut b = Body::new();
    let schema = b.schema(
        &[(0, 1), (1, 1), (2, 1)],
        &[(&[0, 1], &[]), (&[1, 2], &[2])],
    );
    let input = b.fresh();
    let outs = [b.fresh(), b.fresh(), b.fresh()];
    let app = b.app(input, &outs);
    let a0 = b.lam_atom("FAtomGT", (1, 1), (-1, 1), input);
    let a1 = b.lam_atom("FAtomGT", (0, 1), (1, 1), input);
    let strict = b.fand(a0, a1);
    let witness = b.lam_atom("FAtomLT", (1, 1), (-1, 1), input);
    let bk = b.ind_atom(outs[0], 1);
    let o1 = b.ind_atom(outs[1], 0);
    let onehot = b.fand(bk, o1);
    let zero = b.ind_atom(outs[0], 0);
    assert_eq!(
        ev4("cellStrictInteriorForm", app, strict, schema, 0, &b),
        Ok(false)
    );
    assert_eq!(ev4("cellOneHotForm", app, onehot, schema, 0, &b), Ok(false));
    assert_eq!(ev5(app, witness, schema, 0, 0, &b), Ok(false));
    assert_eq!(ev4("cellOutZeroForm", app, zero, schema, 0, &b), Ok(false));
}

// ---------------------------------------------------------------------
// Mutants: each one row (or one constant) away from a Holds case,
// each flipping Holds to Fails.
// ---------------------------------------------------------------------

#[test]
fn mutant_prim_rescaled_atom_fails() {
    // THE spec-grain mutant: vertices at 1/2 and 3/2 give λ₀ = 3/2 −
    // x; the halfspace form's positive primitive-integer rescale
    // renders that same halfspace as 3 − 2x, which the RAW-coefficient
    // build must reject.
    let mut b = Body::new();
    let schema = b.schema(&[(1, 2), (3, 2)], &[(&[0, 1], &[])]);
    let input = b.fresh();
    let b0 = b.fresh();
    let app = b.app(input, &[b0]);
    let a0 = b.lam_atom("FAtomGT", (3, 1), (-2, 1), input);
    let a1 = b.lam_atom("FAtomGT", (-1, 2), (1, 1), input);
    let f = b.fand(a0, a1);
    assert_eq!(
        ev4("cellStrictInteriorForm", app, f, schema, 0, &b),
        Ok(false)
    );
}

#[test]
fn mutant_halfspace_layout_fails() {
    // The halfspace form's `TAdd(TMul(s, t), TConst(c))` layout — sum
    // arms swapped against the cell builds' `TAdd(TConst(c),
    // TMul(s, t))` — is a decided mismatch.
    let mut b = Body::new();
    let (schema, app, input, _b0) = demo1(&mut b);
    let slpc = b.tconst(-1, 1);
    let v = b.tvar(input);
    let prod = b.tmul(slpc, v);
    let offc = b.tconst(2, 1);
    let lhs = b.tadd(prod, offc); // swapped
    let zero = b.tconst(0, 1);
    let a0 = b.fatom("FAtomGT", lhs, zero);
    let a1 = b.lam_atom("FAtomGT", (-1, 1), (1, 1), input);
    let f = b.fand(a0, a1);
    assert_eq!(
        ev4("cellStrictInteriorForm", app, f, schema, 0, &b),
        Ok(false)
    );
}

#[test]
fn mutant_swapped_arms_fails() {
    let mut b = Body::new();
    let (schema, app, input, _b0) = demo1(&mut b);
    let a1 = b.lam_atom("FAtomGT", (-1, 1), (1, 1), input);
    let a0 = b.lam_atom("FAtomGT", (2, 1), (-1, 1), input);
    let f = b.fand(a1, a0); // decreasing vertex order
    assert_eq!(
        ev4("cellStrictInteriorForm", app, f, schema, 0, &b),
        Ok(false)
    );
}

#[test]
fn mutant_ext_membership_row_flips_verdict() {
    // The demo strict form is the ∅-extension rendering; adding the
    // one CellExtHasV row that extends the cell through vertex 0 must
    // flip Holds to Fails (the comparator there becomes LT).
    let mut b = Body::new();
    let (schema, app, input, _b0) = demo1(&mut b);
    let a0 = b.lam_atom("FAtomGT", (2, 1), (-1, 1), input);
    let a1 = b.lam_atom("FAtomGT", (-1, 1), (1, 1), input);
    let f = b.fand(a0, a1);
    assert_eq!(
        ev4("cellStrictInteriorForm", app, f, schema, 0, &b),
        Ok(true)
    );
    b.mask_row("CellExtHasV", schema, 0, 0);
    assert_eq!(
        ev4("cellStrictInteriorForm", app, f, schema, 0, &b),
        Ok(false)
    );
}

#[test]
fn mutant_wrong_input_wire_fails() {
    // The λ-atoms over a DIFFERENT wire's variable: wires are nominal.
    let mut b = Body::new();
    let (schema, app, _input, _b0) = demo1(&mut b);
    let other = b.fresh();
    let a0 = b.lam_atom("FAtomGT", (2, 1), (-1, 1), other);
    let a1 = b.lam_atom("FAtomGT", (-1, 1), (1, 1), other);
    let f = b.fand(a0, a1);
    assert_eq!(
        ev4("cellStrictInteriorForm", app, f, schema, 0, &b),
        Ok(false)
    );
}

#[test]
fn mutant_one_hot_bare_bk_fails_single_cell() {
    // chainAnd([]) = FTrue is load-bearing: the bare (b₀ = 1) atom,
    // without the FAnd(_, FTrue) wrap, is a decided mismatch.
    let mut b = Body::new();
    let (schema, app, _input, b0) = demo1(&mut b);
    let f = b.ind_atom(b0, 1);
    assert_eq!(ev4("cellOneHotForm", app, f, schema, 0, &b), Ok(false));
}

#[test]
fn mutant_one_hot_ftrue_tail_on_two_cells_fails() {
    // chainAnd([f]) = f is equally load-bearing: FAnd(b₁ = 1,
    // FAnd(b₀ = 0, FTrue)) — the tt-terminated variant — must fail
    // where FAnd(b₁ = 1, b₀ = 0) holds.
    let mut b = Body::new();
    let (schema, app, _input, outs) = demo2(&mut b);
    let bk = b.ind_atom(outs[1], 1);
    let other = b.ind_atom(outs[0], 0);
    let tt = b.ftrue();
    let tail = b.fand(other, tt);
    let f = b.fand(bk, tail);
    assert_eq!(ev4("cellOneHotForm", app, f, schema, 1, &b), Ok(false));
}

#[test]
fn mutant_one_hot_swapped_values_fails() {
    let mut b = Body::new();
    let (schema, app, _input, outs) = demo2(&mut b);
    let bk = b.ind_atom(outs[1], 0); // 0 where 1 expected
    let other = b.ind_atom(outs[0], 1);
    let f = b.fand(bk, other);
    assert_eq!(ev4("cellOneHotForm", app, f, schema, 1, &b), Ok(false));
}

#[test]
fn mutant_one_hot_chain_order_fails() {
    // whichI = 1 of three, others out of ascending order.
    let mut b = Body::new();
    let schema = b.schema(
        &[(0, 1), (1, 1), (2, 1), (3, 1)],
        &[(&[0, 1], &[]), (&[1, 2], &[]), (&[2, 3], &[])],
    );
    let input = b.fresh();
    let outs = [b.fresh(), b.fresh(), b.fresh()];
    let app = b.app(input, &outs);
    let bk = b.ind_atom(outs[1], 1);
    let o2 = b.ind_atom(outs[2], 0);
    let o0 = b.ind_atom(outs[0], 0);
    let tail = b.fand(o2, o0); // descending
    let f = b.fand(bk, tail);
    assert_eq!(ev4("cellOneHotForm", app, f, schema, 1, &b), Ok(false));
}

#[test]
fn mutant_witness_strict_interior_sign_fails() {
    // The strict-interior sign (GT at a core vertex) where the
    // out-witness form REVERSES to LT.
    let mut b = Body::new();
    let (schema, app, input, _b0) = demo1(&mut b);
    let f = b.lam_atom("FAtomGT", (2, 1), (-1, 1), input);
    assert_eq!(ev5(app, f, schema, 0, 0, &b), Ok(false));
}

#[test]
fn mutant_witness_other_vertex_lambda_fails() {
    // Vertex 1's λ (with vertex 1's correct reversed sign) offered as
    // the witness atom for vertex 0.
    let mut b = Body::new();
    let (schema, app, input, _b0) = demo1(&mut b);
    let f = b.lam_atom("FAtomLT", (-1, 1), (1, 1), input);
    assert_eq!(ev5(app, f, schema, 0, 0, &b), Ok(false));
}

#[test]
fn witness_outside_the_cell_mask_fails() {
    // Cell 0 of demo2 is {0, 1}: witnessVertex = 2 is outside its
    // simplex mask — the build's own guard, decided false. An
    // out-of-range witnessVertex (= 9) is subsumed by the same guard.
    let mut b = Body::new();
    let (schema, app, input, _) = demo2(&mut b);
    let f = b.lam_atom("FAtomLT", (1, 1), (-1, 1), input);
    assert_eq!(ev5(app, f, schema, 0, 2, &b), Ok(false));
    assert_eq!(ev5(app, f, schema, 0, 9, &b), Ok(false));
}

#[test]
fn mutant_out_zero_wrong_wire_fails() {
    let mut b = Body::new();
    let (schema, app, _input, outs) = demo2(&mut b);
    let f = b.ind_atom(outs[0], 0); // b₀ where whichJ = 1
    assert_eq!(ev4("cellOutZeroForm", app, f, schema, 1, &b), Ok(false));
}

#[test]
fn mutant_out_zero_value_one_fails() {
    let mut b = Body::new();
    let (schema, app, _input, outs) = demo2(&mut b);
    let f = b.ind_atom(outs[1], 1);
    assert_eq!(ev4("cellOutZeroForm", app, f, schema, 1, &b), Ok(false));
}

#[test]
fn mutant_output_port_swap_flips_one_hot() {
    // Two apps over the same schema, output wires crossed: the same
    // formula holds against one and fails against the other — the
    // outputs list is the PORT rows' data, not the formula's.
    let mut b = Body::new();
    let schema = b.schema(
        &[(0, 1), (1, 1), (2, 1)],
        &[(&[0, 1], &[]), (&[1, 2], &[2])],
    );
    let input = b.fresh();
    let w0 = b.fresh();
    let w1 = b.fresh();
    let app = b.app(input, &[w0, w1]);
    let crossed = b.app(input, &[w1, w0]);
    let bk = b.ind_atom(w1, 1);
    let other = b.ind_atom(w0, 0);
    let f = b.fand(bk, other);
    assert_eq!(ev4("cellOneHotForm", app, f, schema, 1, &b), Ok(true));
    assert_eq!(ev4("cellOneHotForm", crossed, f, schema, 1, &b), Ok(false));
}

// ---------------------------------------------------------------------
// The construction's `none` branches: decided false.
// ---------------------------------------------------------------------

#[test]
fn wrong_cell_mask_sizes_fail() {
    for verts in [&[0u64][..], &[0, 1, 2][..], &[][..]] {
        let mut b = Body::new();
        let schema = b.schema(&[(0, 1), (1, 1), (2, 1)], &[(verts, &[])]);
        let input = b.fresh();
        let b0 = b.fresh();
        let app = b.app(input, &[b0]);
        let a0 = b.lam_atom("FAtomGT", (1, 1), (-1, 1), input);
        let a1 = b.lam_atom("FAtomGT", (0, 1), (1, 1), input);
        let f = b.fand(a0, a1);
        assert_eq!(
            ev4("cellStrictInteriorForm", app, f, schema, 0, &b),
            Ok(false),
            "cell mask size {} must be a decided false",
            verts.len()
        );
    }
}

#[test]
fn ambient_dimension_two_fails() {
    let mut b = Body::new();
    let schema = b.fresh();
    b.field("SimpC/n_vertices", schema, natv(2));
    b.field("SimpC/amb_dim", schema, natv(2));
    for v in 0..2u64 {
        for j in 0..2u64 {
            b.coord(schema, v, j, (v + j) as i64, 1);
        }
    }
    b.field("SimpC/nCells", schema, natv(1));
    b.mask_row("CellSimplexHasV", schema, 0, 0);
    b.mask_row("CellSimplexHasV", schema, 0, 1);
    let input = b.fresh();
    let b0 = b.fresh();
    let app = b.app(input, &[b0]);
    let a0 = b.lam_atom("FAtomGT", (1, 1), (-1, 1), input);
    let a1 = b.lam_atom("FAtomGT", (0, 1), (1, 1), input);
    let f = b.fand(a0, a1);
    assert_eq!(
        ev4("cellStrictInteriorForm", app, f, schema, 0, &b),
        Ok(false)
    );
}

#[test]
fn coincident_coordinates_fail() {
    let mut b = Body::new();
    let schema = b.schema(&[(1, 1), (1, 1)], &[(&[0, 1], &[])]);
    let input = b.fresh();
    let b0 = b.fresh();
    let app = b.app(input, &[b0]);
    let a0 = b.lam_atom("FAtomGT", (2, 1), (-1, 1), input);
    let a1 = b.lam_atom("FAtomGT", (-1, 1), (1, 1), input);
    let f = b.fand(a0, a1);
    assert_eq!(
        ev4("cellStrictInteriorForm", app, f, schema, 0, &b),
        Ok(false)
    );
}

// ---------------------------------------------------------------------
// Refusals (undecidable is never a verdict)
// ---------------------------------------------------------------------

#[test]
fn missing_input_port_refuses() {
    let mut b = Body::new();
    let (schema, _app, _input, outs) = demo2(&mut b);
    // An app with output ports only.
    let app = b.fresh();
    for (i, &w) in outs.iter().enumerate() {
        let q = b.fresh();
        b.field("OutputPort/app", q, lref(app));
        b.field("OutputPort/pos", q, natv(i as u64));
        b.field("OutputPort/wire", q, lref(w));
    }
    let f = b.ind_atom(outs[1], 0);
    let err = ev4("cellOutZeroForm", app, f, schema, 1, &b).unwrap_err();
    assert!(
        err.contains("do not destructure as a cell application"),
        "missing input port must refuse: {err}"
    );
}

#[test]
fn second_input_port_refuses() {
    let mut b = Body::new();
    let (schema, app, input, outs) = demo2(&mut b);
    let p = b.fresh();
    b.field("InputPort/app", p, lref(app));
    b.field("InputPort/pos", p, natv(1));
    b.field("InputPort/wire", p, lref(input));
    let f = b.ind_atom(outs[1], 0);
    let err = ev4("cellOutZeroForm", app, f, schema, 1, &b).unwrap_err();
    assert!(
        err.contains("do not destructure as a cell application"),
        "a second input port must refuse: {err}"
    );
}

#[test]
fn conflicting_input_wires_refuse() {
    // A SECOND port element claiming position 0 with a different
    // wire: the port-uniqueness axiom admits no such state.
    let mut b = Body::new();
    let (schema, app, _input, outs) = demo2(&mut b);
    let other = b.fresh();
    let p = b.fresh();
    b.field("InputPort/app", p, lref(app));
    b.field("InputPort/pos", p, natv(0));
    b.field("InputPort/wire", p, lref(other));
    let f = b.ind_atom(outs[1], 0);
    let err = ev4("cellOutZeroForm", app, f, schema, 1, &b).unwrap_err();
    assert!(
        err.contains("conflicting `InputPort` wires"),
        "conflicting input wires must refuse: {err}"
    );
}

#[test]
fn gapped_output_positions_refuse() {
    let mut b = Body::new();
    let schema = b.schema(&[(1, 1), (2, 1)], &[(&[0, 1], &[])]);
    let input = b.fresh();
    let w = b.fresh();
    let app = b.fresh();
    let p = b.fresh();
    b.field("InputPort/app", p, lref(app));
    b.field("InputPort/pos", p, natv(0));
    b.field("InputPort/wire", p, lref(input));
    let q = b.fresh();
    b.field("OutputPort/app", q, lref(app));
    b.field("OutputPort/pos", q, natv(1)); // gap at 0
    b.field("OutputPort/wire", q, lref(w));
    let f = b.ind_atom(w, 0);
    let err = ev4("cellOutZeroForm", app, f, schema, 0, &b).unwrap_err();
    assert!(
        err.contains("not the dense list"),
        "gapped output positions must refuse: {err}"
    );
}

#[test]
fn missing_n_cells_refuses() {
    let mut b = Body::new();
    let schema = b.fresh();
    b.field("SimpC/n_vertices", schema, natv(2));
    b.field("SimpC/amb_dim", schema, natv(1));
    b.coord(schema, 0, 0, 1, 1);
    b.coord(schema, 1, 0, 2, 1);
    // no SimpC/nCells row
    let input = b.fresh();
    let b0 = b.fresh();
    let app = b.app(input, &[b0]);
    let f = b.ind_atom(b0, 0);
    let err = ev4("cellOutZeroForm", app, f, schema, 0, &b).unwrap_err();
    assert!(
        err.contains("no `SimpC/nCells` row"),
        "missing cell count must refuse: {err}"
    );
}

#[test]
fn out_of_range_mask_rows_refuse() {
    // Cell index at nCells, then vertex index at n_vertices — each
    // outside the spec model's representable masks.
    for (cell, v) in [(7u64, 0u64), (0, 9)] {
        let mut b = Body::new();
        let (schema, app, input, _b0) = demo1(&mut b);
        b.mask_row("CellSimplexHasV", schema, cell, v);
        let a0 = b.lam_atom("FAtomGT", (2, 1), (-1, 1), input);
        let a1 = b.lam_atom("FAtomGT", (-1, 1), (1, 1), input);
        let f = b.fand(a0, a1);
        let err = ev4("cellStrictInteriorForm", app, f, schema, 0, &b).unwrap_err();
        assert!(
            err.contains("at or past"),
            "out-of-range mask row ({cell}, {v}) must refuse: {err}"
        );
    }
}

#[test]
fn one_hot_ignores_mask_rows_entirely() {
    // The one-hot build reads outputs + cell count only: mask rows —
    // even out-of-range ones — are outside its read set (it never
    // sweeps them), so the verdict stands. Contrast with the
    // strict-interior refusal above; validate-what-you-read.
    let mut b = Body::new();
    let (schema, app, _input, b0) = demo1(&mut b);
    b.mask_row("CellSimplexHasV", schema, 7, 0);
    let bk = b.ind_atom(b0, 1);
    let tt = b.ftrue();
    let f = b.fand(bk, tt);
    assert_eq!(ev4("cellOneHotForm", app, f, schema, 0, &b), Ok(true));
}

#[test]
fn unconstructed_formula_refuses() {
    let mut b = Body::new();
    let (schema, app, _input, _b0) = demo1(&mut b);
    let ghost = b.fresh();
    let err = ev4("cellOutZeroForm", app, ghost, schema, 0, &b).unwrap_err();
    assert!(
        err.contains("no formula constructor row") || err.contains("structure undecidable"),
        "unconstructed formula must refuse: {err}"
    );
}

#[test]
fn provider_claims_the_four_relations() {
    for name in [
        "cellStrictInteriorForm",
        "cellOneHotForm",
        "cellOutWitnessForm",
        "cellOutZeroForm",
    ] {
        assert!(provider().local_by_name(name).is_some(), "`{name}` claimed");
    }
}

// ---------------------------------------------------------------------
// The frozen cross-implementation corpus (python `fractions` arm — an
// independent transcription of the four builds and the shared gate):
// replay every instance through provider dispatch and require verdict
// agreement. Disagreement = stop-and-investigate, never
// adjust-the-corpus.
// ---------------------------------------------------------------------

#[test]
fn pyref_corpus_replays() {
    use serde_json::Value as J;
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/cellform_pyref_corpus.json"
    );
    let corpus: J = serde_json::from_str(&std::fs::read_to_string(path).expect("corpus present"))
        .expect("corpus parses");
    let pair = |j: &J| -> (i64, u64) {
        let a = j.as_array().expect("num/den pair");
        (a[0].as_i64().expect("num"), a[1].as_u64().expect("den"))
    };
    let nats = |j: &J| -> Vec<u64> {
        j.as_array()
            .expect("nat list")
            .iter()
            .map(|v| v.as_u64().expect("nat"))
            .collect()
    };
    let mut counts: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    for (i, case) in corpus["cases"]
        .as_array()
        .expect("cases")
        .iter()
        .enumerate()
    {
        let kind = case["kind"].as_str().expect("kind");
        let form = case["form"].as_str().expect("form");
        let coords: Vec<(i64, u64)> = case["coords"]
            .as_array()
            .expect("coords")
            .iter()
            .map(pair)
            .collect();
        let cells: Vec<(Vec<u64>, Vec<u64>)> = case["cells"]
            .as_array()
            .expect("cells")
            .iter()
            .map(|c| (nats(&c["simplex"]), nats(&c["ext"])))
            .collect();
        let which = case["which"].as_u64().expect("which");
        let witness = case["witness"].as_u64();
        let n_outputs = case["n_outputs"].as_u64().expect("n_outputs") as usize;
        let verdict = case["verdict"].as_bool().expect("verdict");

        let mut b = Body::new();
        let cell_refs: Vec<(&[u64], &[u64])> = cells
            .iter()
            .map(|(s, e)| (s.as_slice(), e.as_slice()))
            .collect();
        let schema = b.schema(&coords, &cell_refs);
        let input = b.fresh();
        let outs: Vec<u32> = (0..n_outputs).map(|_| b.fresh()).collect();
        let app = b.app(input, &outs);

        // Build the case's formula from its spec.
        let spec = &case["formula"];
        let affine = |b: &mut Body, a: &J| -> u32 {
            let op = match a["op"].as_str().expect("op") {
                "lt" => "FAtomLT",
                "gt" => "FAtomGT",
                other => panic!("unexpected op {other}"),
            };
            let off = pair(&a["off"]);
            let slp = pair(&a["slp"]);
            b.lam_atom(op, off, slp, input)
        };
        let ind = |b: &mut Body, a: &J| -> u32 {
            let w = a[0].as_i64().expect("wire index");
            let v = a[1].as_i64().expect("value");
            let wire = if w < 0 { b.fresh() } else { outs[w as usize] };
            b.ind_atom(wire, v)
        };
        let formula = match spec["type"].as_str().expect("type") {
            "and2" => {
                let atoms = spec["atoms"].as_array().expect("atoms");
                let a0 = affine(&mut b, &atoms[0]);
                let a1 = affine(&mut b, &atoms[1]);
                b.fand(a0, a1)
            }
            "atom" => affine(&mut b, &spec["atom"]),
            "ind" => ind(&mut b, &spec["atom"]),
            "chain" => {
                let atoms = spec["atoms"].as_array().expect("atoms");
                let tail_true = spec["tail_true"].as_bool().expect("tail_true");
                let elems: Vec<u32> = atoms.iter().map(|a| ind(&mut b, a)).collect();
                // Right-nested: FAnd(a0, FAnd(a1, … tail)); the tail is
                // FTrue when tail_true, else the last atom.
                let mut acc = if tail_true {
                    let tt = b.ftrue();
                    let last = *elems.last().expect("nonempty chain");
                    b.fand(last, tt)
                } else {
                    *elems.last().expect("nonempty chain")
                };
                for &a in elems[..elems.len() - 1].iter().rev() {
                    acc = b.fand(a, acc);
                }
                acc
            }
            other => panic!("unexpected formula type {other}"),
        };

        let rel = match form {
            "strict" => "cellStrictInteriorForm",
            "onehot" => "cellOneHotForm",
            "witness" => "cellOutWitnessForm",
            "zero" => "cellOutZeroForm",
            other => panic!("unexpected form {other}"),
        };
        let got = if form == "witness" {
            ev5(app, formula, schema, which, witness.expect("witness"), &b)
        } else {
            ev4(rel, app, formula, schema, which, &b)
        };
        assert_eq!(
            got,
            Ok(verdict),
            "corpus case {i} ({kind}, {form}) disagrees with the python arm"
        );
        *counts
            .entry(kind.split('_').next().unwrap().to_string())
            .or_default() += 1;
    }
    assert!(counts["holds"] >= 60, "holds corpus size: {counts:?}");
    assert!(counts["mutant"] >= 60, "mutant corpus size: {counts:?}");
    assert!(
        counts["gate"] + counts["none"] >= 15,
        "gate/none corpus size: {counts:?}"
    );
}
