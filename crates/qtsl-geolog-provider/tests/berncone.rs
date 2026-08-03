//! The Bernstein-cone family exercised end to end through provider
//! dispatch: `allForwardDiffBernCoeffsSatisfyP` (the exact-rational
//! forward-difference coefficient sweep, recomputed — no coefficient
//! data on the rows) and `coverInfeasibilityValid` (the subdivision
//! rule's 1-D interval cover recompute).
//!
//! Golden anchors transcribed from the executable Lean receipts:
//! `EvalDemo.lean`'s `bernConeCoeffCheck`/`coverCheck` lines over the
//! `DemoData.lean` geometry (branch B `[1, 2]`, halves L/R, the gap
//! complex G) and the kernel-checked multivariate fixture
//! `Comparator/Fixtures/MultivarBernCone.lean` (the standard 3-simplex
//! in ℚ³, `p(x) = 1 + x₀·x₁ + x₂²`, degree 2). Named data mutants
//! (every mutant flips a verdict), decided-`false` probes for each
//! spec gate, refusal witnesses, and the frozen cross-implementation
//! corpus.
//!
//! The test-side row emitter shares no code with the evaluators: it
//! writes `Op::Funa` constructor/field rows and `Op::Rela` membership
//! rows directly from the synthetic declaration index.

mod common;

use common::{provider, stack, STACK};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;

const OWN: [u8; 32] = [0xBC; 32];

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

/// Geometry + syntax bodies in miniature: complexes with vertex
/// tables, simplexes and extension sets, subdivision nodes, and
/// Term/Formula constructor rows.
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

    fn member(&mut self, rel: &str, subject: u32, v: u64) {
        self.ops.push(Op::Rela {
            rel: self.xref(s_fun(rel)),
            args: vec![lref(subject), natv(v)],
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

    /// A complex with `n` vertices in a line (`amb_dim = 1`), vertex
    /// coordinates given in vertex order.
    fn line_complex(&mut self, coords: &[(i64, u64)]) -> u32 {
        let c = self.fresh();
        self.field("SimpC/n_vertices", c, natv(coords.len() as u64));
        self.field("SimpC/amb_dim", c, natv(1));
        for (v, (num, den)) in coords.iter().enumerate() {
            self.coord(c, v as u64, 0, *num, *den);
        }
        c
    }

    /// A complex in `amb` dimensions; `coords[v][j]` in vertex-major
    /// order.
    fn nd_complex(&mut self, amb: u64, coords: &[&[(i64, u64)]]) -> u32 {
        let c = self.fresh();
        self.field("SimpC/n_vertices", c, natv(coords.len() as u64));
        self.field("SimpC/amb_dim", c, natv(amb));
        for (v, row) in coords.iter().enumerate() {
            assert_eq!(row.len() as u64, amb, "coords are vertex-major");
            for (j, (num, den)) in row.iter().enumerate() {
                self.coord(c, v as u64, j as u64, *num, *den);
            }
        }
        c
    }

    fn simplex(&mut self, complex: u32, verts: &[u64]) -> u32 {
        let s = self.fresh();
        self.field("Simplex/complex", s, lref(complex));
        for &v in verts {
            self.member("Simplex/contains", s, v);
        }
        s
    }

    fn ext(&mut self, simplex: u32, verts: &[u64]) -> u32 {
        let e = self.fresh();
        self.field("ExtensionSet/simplex", e, lref(simplex));
        for &v in verts {
            self.member("ExtensionSet/contains", e, v);
        }
        e
    }

    /// A subdivision node with its dense branch families (field order
    /// bytewise: `k`, `p`).
    fn subdivide(&mut self, branches: &[(u32, u32)]) -> u32 {
        let p = self.fresh();
        self.field("PSubdivide/nBranches", p, natv(branches.len() as u64));
        for (k, (s, e)) in branches.iter().enumerate() {
            self.branch_row("PSubdivide/branchSimplex", k as u64, p, lref(*s));
            self.branch_row("PSubdivide/branchS", k as u64, p, lref(*e));
        }
        p
    }

    fn branch_row(&mut self, fun: &str, k: u64, p: u32, value: Value) {
        self.ops.push(Op::Funa {
            fun: self.xref(s_fun(fun)),
            args: vec![natv(k), lref(p)],
            value,
        });
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

    /// A constructor row producing a NAMED element (for ambiguity
    /// witnesses).
    fn ctor_at(&mut self, fun: &str, args: Vec<Value>, e: u32) {
        self.ops.push(Op::Funa {
            fun: self.xref(s_fun(fun)),
            args,
            value: lref(e),
        });
    }

    fn tvar(&mut self, wire: &Value) -> u32 {
        self.ctor("TVar", vec![wire.clone()])
    }

    fn tconst(&mut self, q: (i64, u64)) -> u32 {
        self.ctor("TConst", vec![qv(q.0, q.1)])
    }

    fn tadd(&mut self, l: u32, r: u32) -> u32 {
        self.ctor("TAdd", vec![lref(l), lref(r)])
    }

    fn tmul(&mut self, l: u32, r: u32) -> u32 {
        self.ctor("TMul", vec![lref(l), lref(r)])
    }

    fn tidx(&mut self, t: u32, i: u64) -> u32 {
        // Field order bytewise: i, t.
        self.ctor("TIdx", vec![natv(i), lref(t)])
    }

    fn thole(&mut self) -> u32 {
        self.ctor("THole", vec![])
    }

    fn fatom(&mut self, name: &str, l: u32, r: u32) -> u32 {
        self.ctor(name, vec![lref(l), lref(r)])
    }

    fn fand(&mut self, l: u32, r: u32) -> u32 {
        self.ctor("FAnd", vec![lref(l), lref(r)])
    }

    fn f_or(&mut self, l: u32, r: u32) -> u32 {
        self.ctor("FOr", vec![lref(l), lref(r)])
    }

    fn ftrue(&mut self) -> u32 {
        self.ctor("FTrue", vec![])
    }

    /// The affine polynomial `c + s·x` over a wire (the demo's
    /// `polyB` layout).
    fn affine_wire_poly(&mut self, c: (i64, u64), s: (i64, u64), wire: &Value) -> u32 {
        let cc = self.tconst(c);
        let sc = self.tconst(s);
        let v = self.tvar(wire);
        let prod = self.tmul(sc, v);
        self.tadd(cc, prod)
    }

    /// The predicate `hole ⋈ c`.
    fn pred(&mut self, atom: &str, c: (i64, u64)) -> u32 {
        let h = self.thole();
        let cc = self.tconst(c);
        self.fatom(atom, h, cc)
    }

    /// The demo geometry: branch B `[1, 2]`, full simplex, extension
    /// mask as given. Returns (simplex, ext).
    fn demo_b(&mut self, ext_verts: &[u64]) -> (u32, u32) {
        let cx = self.line_complex(&[(1, 1), (2, 1)]);
        let s = self.simplex(cx, &[0, 1]);
        let e = self.ext(s, ext_verts);
        (s, e)
    }

    /// The multivariate fixture geometry: the standard 3-simplex in
    /// ℚ³ (vertex 0 at the origin, vertex v = e_{v-1}). Returns
    /// (simplex, ext with the given mask).
    fn multivar_m(&mut self, ext_verts: &[u64]) -> (u32, u32) {
        let z = (0i64, 1u64);
        let o = (1i64, 1u64);
        let cx = self.nd_complex(3, &[&[z, z, z], &[o, z, z], &[z, o, z], &[z, z, o]]);
        let s = self.simplex(cx, &[0, 1, 2, 3]);
        let e = self.ext(s, ext_verts);
        (s, e)
    }

    /// The multivariate fixture polynomial `1 + x₀·x₁ + x₂²` over one
    /// vector wire.
    fn poly_m(&mut self, wire: &Value) -> u32 {
        let one = self.tconst((1, 1));
        let v = self.tvar(wire);
        let x0 = self.tidx(v, 0);
        let v1 = self.tvar(wire);
        let x1 = self.tidx(v1, 1);
        let m01 = self.tmul(x0, x1);
        let v2 = self.tvar(wire);
        let x2 = self.tidx(v2, 2);
        let v3 = self.tvar(wire);
        let x2b = self.tidx(v3, 2);
        let m22 = self.tmul(x2, x2b);
        let a = self.tadd(one, m01);
        self.tadd(a, m22)
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

/// Dispatch the coefficient sweep with the registry's bytewise claim
/// order: S, degree, polynomial, predicate, simplex.
fn evc(
    s_ext: u32,
    degree: u64,
    polynomial: u32,
    predicate: u32,
    simplex: u32,
    b: &Body,
) -> Result<bool, String> {
    let args = [
        lref(s_ext),
        natv(degree),
        lref(polynomial),
        lref(predicate),
        lref(simplex),
    ];
    let refs: Vec<&Value> = args.iter().collect();
    common::ev("allForwardDiffBernCoeffsSatisfyP", &refs, &b.rows())
}

/// Dispatch the cover check with the registry's bytewise claim order:
/// S, coverCertificate, p, simplex, termX.
fn evv(s_ext: u32, cert: u32, p: u32, simplex: u32, term_x: u32, b: &Body) -> Result<bool, String> {
    let args = [
        lref(s_ext),
        lref(cert),
        lref(p),
        lref(simplex),
        lref(term_x),
    ];
    let refs: Vec<&Value> = args.iter().collect();
    common::ev("coverInfeasibilityValid", &refs, &b.rows())
}

#[test]
fn claimed() {
    assert!(
        provider()
            .local_by_name("allForwardDiffBernCoeffsSatisfyP")
            .is_some(),
        "`allForwardDiffBernCoeffsSatisfyP` claimed"
    );
    assert!(
        provider()
            .local_by_name("coverInfeasibilityValid")
            .is_some(),
        "`coverInfeasibilityValid` claimed"
    );
}

// ---------------------------------------------------------------------
// Golden anchors — the coefficient sweep (EvalDemo.lean +
// MultivarBernCone.lean, each a Lean-executed verdict)
// ---------------------------------------------------------------------

/// `bernConeCoeffCheck simplexB Sempty 1 polyB predP1 = true`:
/// p = 1/2 + 2x on [1, 2], hole ≥ 0 (grid coefficients 5/2 and 9/2).
#[test]
fn demo_poly_b_holds() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    assert_eq!(evc(e, 1, p, pr, s, &b), Ok(true));
}

/// `… (-5 + 2x) predP1 = false` (coefficients −3 and −1).
#[test]
fn demo_negative_poly_fails() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((-5, 1), (2, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    assert_eq!(evc(e, 1, p, pr, s, &b), Ok(false));
}

/// `… (1/2 − 2x) predP1 = false` (negative slope drives both
/// endpoints negative).
#[test]
fn demo_flipped_poly_fails() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (-2, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    assert_eq!(evc(e, 1, p, pr, s, &b), Ok(false));
}

/// `… (x·x) predP1 = false` at degree 1: a degree lie is rejected,
/// never truncated.
#[test]
fn demo_degree_lie_fails() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let w = lref(b.fresh());
    let v1 = b.tvar(&w);
    let v2 = b.tvar(&w);
    let p = b.tmul(v1, v2);
    let pr = b.pred("FAtomGE", (0, 1));
    assert_eq!(evc(e, 1, p, pr, s, &b), Ok(false));
}

/// `bernConeCoeffCheck simplexPt SemptyPt … = false`: one vertex in an
/// ambient line is not full-dimensional (`verts ≠ ambDim + 1`).
#[test]
fn demo_point_simplex_fails() {
    let mut b = Body::new();
    let cx = b.line_complex(&[(1, 1), (2, 1)]);
    let s = b.simplex(cx, &[0]);
    let e = b.ext(s, &[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    assert_eq!(evc(e, 1, p, pr, s, &b), Ok(false));
}

/// The kernel-checked multivariate fixture:
/// `bernConeCoeffCheck simplexM SemptyM 2 polyM predP1 = true` —
/// `1 + x₀·x₁ + x₂²` on the standard 3-simplex, degree 2, hole ≥ 0.
#[test]
fn multivar_fixture_holds() {
    let mut b = Body::new();
    let (s, e) = b.multivar_m(&[]);
    let w = lref(b.fresh());
    let p = b.poly_m(&w);
    let pr = b.pred("FAtomGE", (0, 1));
    assert_eq!(evc(e, 2, p, pr, s, &b), Ok(true));
}

/// The fixture's tightened control: hole ≥ 3/2 must FAIL (the pure-λ₀
/// coefficient is 1).
#[test]
fn multivar_tightened_control_fails() {
    let mut b = Body::new();
    let (s, e) = b.multivar_m(&[]);
    let w = lref(b.fresh());
    let p = b.poly_m(&w);
    let pr = b.pred("FAtomGE", (3, 2));
    assert_eq!(evc(e, 2, p, pr, s, &b), Ok(false));
}

/// A constant polynomial is idx-free with no wires: admissible in any
/// ambient dimension (the scalar-scope gate binds nonconstant wire
/// polynomials only).
#[test]
fn constant_poly_any_dimension_holds() {
    let mut b = Body::new();
    let (s, e) = b.multivar_m(&[]);
    let p = b.tconst((1, 1));
    let pr = b.pred("FAtomGE", (1, 1));
    assert_eq!(evc(e, 0, p, pr, s, &b), Ok(true));
}

/// A nonconstant wire polynomial outside `ambDim = 1` is decided
/// false (the D2 scalar scope).
#[test]
fn wire_poly_in_three_dimensions_fails() {
    let mut b = Body::new();
    let (s, e) = b.multivar_m(&[]);
    let w = lref(b.fresh());
    let p = b.tvar(&w);
    let pr = b.pred("FAtomGE", (0, 1));
    assert_eq!(evc(e, 2, p, pr, s, &b), Ok(false));
}

/// Two distinct wires: outside `asCoordPoly?`'s fragment — decided
/// false.
#[test]
fn two_wires_fail() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let w0 = lref(b.fresh());
    let w1 = lref(b.fresh());
    let v0 = b.tvar(&w0);
    let v1 = b.tvar(&w1);
    let p = b.tadd(v0, v1);
    let pr = b.pred("FAtomGE", (0, 1));
    assert_eq!(evc(e, 1, p, pr, s, &b), Ok(false));
}

/// An idx-bearing polynomial with a NONEMPTY extension mask is decided
/// false (the idx arm demands `S.isEmptyB`).
#[test]
fn idx_poly_with_nonempty_extension_fails() {
    let mut b = Body::new();
    let (s, e) = b.multivar_m(&[0]);
    let w = lref(b.fresh());
    let p = b.poly_m(&w);
    let pr = b.pred("FAtomGE", (0, 1));
    assert_eq!(evc(e, 2, p, pr, s, &b), Ok(false));
}

/// A `TIdx` index at the ambient dimension is out of bounds — decided
/// false (`idxBounded`).
#[test]
fn idx_out_of_bounds_fails() {
    let mut b = Body::new();
    let (s, e) = b.multivar_m(&[]);
    let w = lref(b.fresh());
    let v = b.tvar(&w);
    let x3 = b.tidx(v, 3);
    let one = b.tconst((1, 1));
    let p = b.tadd(one, x3);
    let pr = b.pred("FAtomGE", (0, 1));
    assert_eq!(evc(e, 2, p, pr, s, &b), Ok(false));
}

/// `TIdx` of a non-var is outside every reading's fragment — decided
/// false.
#[test]
fn idx_of_non_var_fails() {
    let mut b = Body::new();
    let (s, e) = b.multivar_m(&[]);
    let c = b.tconst((1, 1));
    let p = b.tidx(c, 0);
    let pr = b.pred("FAtomGE", (0, 1));
    assert_eq!(evc(e, 2, p, pr, s, &b), Ok(false));
}

/// A nonempty extension mask on the 1-D geometry: the forward
/// differences (not just the base row) drive the verdict. For
/// p = 1/2 + 2x on [1, 2] with S = {0}, the grid carries {9/2, 2}:
/// hole ≥ 0 holds…
#[test]
fn nonempty_extension_forward_differences_hold() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[0]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    assert_eq!(evc(e, 1, p, pr, s, &b), Ok(true));
}

/// …and hole ≥ 5/2 separates the masks: the EMPTY extension's grid is
/// {5/2, 9/2} (holds), while S = {0}'s forward difference 2 fails it.
#[test]
fn mutant_extension_mask_flips_the_verdict() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.pred("FAtomGE", (5, 2));
    assert_eq!(evc(e, 1, p, pr, s, &b), Ok(true));

    let mut b2 = Body::new();
    let (s2, e2) = b2.demo_b(&[0]);
    let w2 = lref(b2.fresh());
    let p2 = b2.affine_wire_poly((1, 2), (2, 1), &w2);
    let pr2 = b2.pred("FAtomGE", (5, 2));
    assert_eq!(evc(e2, 1, p2, pr2, s2, &b2), Ok(false));
}

// ---------------------------------------------------------------------
// Named data mutants — every one flips the demo hold.
// ---------------------------------------------------------------------

/// A vertex coordinate pulled below the root: the sweep must see the
/// new endpoint value go negative.
#[test]
fn mutant_coord_flips_the_verdict() {
    let mut b = Body::new();
    let cx = b.line_complex(&[(-2, 1), (2, 1)]);
    let s = b.simplex(cx, &[0, 1]);
    let e = b.ext(s, &[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    assert_eq!(evc(e, 1, p, pr, s, &b), Ok(false));
}

/// The predicate threshold tightened past the smallest coefficient.
#[test]
fn mutant_pred_threshold_flips_the_verdict() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.pred("FAtomGE", (3, 1));
    assert_eq!(evc(e, 1, p, pr, s, &b), Ok(false));
}

/// The degree claim lowered under the polynomial's true degree.
#[test]
fn mutant_degree_zero_flips_the_verdict() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    assert_eq!(evc(e, 0, p, pr, s, &b), Ok(false));
}

/// A strict comparator at an achieved bound: hole > 5/2 fails where
/// hole ≥ 5/2 holds (the boundary coefficient is exactly 5/2).
#[test]
fn mutant_strict_comparator_at_the_boundary_flips() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.pred("FAtomGT", (5, 2));
    assert_eq!(evc(e, 1, p, pr, s, &b), Ok(false));
}

// ---------------------------------------------------------------------
// Predicate semantics — `satisfiesPredQ`'s decided-false `none` class.
// ---------------------------------------------------------------------

/// A predicate with a free wire never closed-evaluates: every
/// coefficient FAILS it — a decided false, not a refusal.
#[test]
fn free_wire_predicate_decides_false() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let stray = lref(b.fresh());
    let sv = b.tvar(&stray);
    let z = b.tconst((0, 1));
    let pr = b.fatom("FAtomGE", sv, z);
    assert_eq!(evc(e, 1, p, pr, s, &b), Ok(false));
}

/// The Option monad does NOT short-circuit: `FOr(always-true,
/// unevaluable)` is `none`, hence false — a Lean-exact pin against
/// short-circuit implementations.
#[test]
fn or_with_unevaluable_arm_decides_false() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let always = b.pred("FAtomGE", (-100, 1));
    let stray = lref(b.fresh());
    let sv = b.tvar(&stray);
    let z = b.tconst((0, 1));
    let bad = b.fatom("FAtomGE", sv, z);
    let pr = b.f_or(always, bad);
    assert_eq!(evc(e, 1, p, pr, s, &b), Ok(false));
}

/// `FAnd` with `FTrue` composes; the conjunction of two satisfied
/// atoms holds.
#[test]
fn conjunctive_predicate_holds() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let a1 = b.pred("FAtomGE", (0, 1));
    let tt = b.ftrue();
    let pr = b.fand(a1, tt);
    assert_eq!(evc(e, 1, p, pr, s, &b), Ok(true));
}

/// The wire-model spec hole in the PREDICATE is a decided
/// non-satisfaction (`evalClosed` has no value for it).
#[test]
fn spec_hole_predicate_decides_false() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.ctor("FSpH", vec![]);
    assert_eq!(evc(e, 1, p, pr, s, &b), Ok(false));
}

// ---------------------------------------------------------------------
// Refusal witnesses — argument and row pathology never decides.
// ---------------------------------------------------------------------

#[test]
fn refusal_degree_q_literal() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    let args = [lref(e), qv(1, 1), lref(p), lref(pr), lref(s)];
    let refs: Vec<&Value> = args.iter().collect();
    assert!(common::ev("allForwardDiffBernCoeffsSatisfyP", &refs, &b.rows()).is_err());
}

#[test]
fn refusal_polynomial_literal_cell() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let pr = b.pred("FAtomGE", (0, 1));
    let args = [lref(e), natv(1), natv(7), lref(pr), lref(s)];
    let refs: Vec<&Value> = args.iter().collect();
    assert!(common::ev("allForwardDiffBernCoeffsSatisfyP", &refs, &b.rows()).is_err());
}

#[test]
fn refusal_unconstructed_polynomial() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let bare = b.fresh();
    let pr = b.pred("FAtomGE", (0, 1));
    assert!(evc(e, 1, bare, pr, s, &b).is_err());
}

/// The predicate hole in the POLYNOMIAL refuses (module adjudication:
/// the shared toPoly walk's posture — outside the term model).
#[test]
fn refusal_hole_in_polynomial() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let p = b.thole();
    let pr = b.pred("FAtomGE", (0, 1));
    assert!(evc(e, 1, p, pr, s, &b).is_err());
}

/// A row-grain-distinct simplex for the extension set: the
/// same-simplex guard is undecidable — refused, never guessed.
#[test]
fn refusal_row_grain_distinct_simplex() {
    let mut b = Body::new();
    let cx = b.line_complex(&[(1, 1), (2, 1)]);
    let s1 = b.simplex(cx, &[0, 1]);
    let s2 = b.simplex(cx, &[0, 1]);
    let e = b.ext(s1, &[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    let err = evc(e, 1, p, pr, s2, &b).expect_err("refuses");
    assert!(err.contains("row-grain distinct"), "{err}");
}

/// An incomplete vertex table refuses (the model's coordinate function
/// is total).
#[test]
fn refusal_missing_coordinate_row() {
    let mut b = Body::new();
    let cx = b.fresh();
    b.field("SimpC/n_vertices", cx, natv(2));
    b.field("SimpC/amb_dim", cx, natv(1));
    b.coord(cx, 0, 0, 1, 1);
    // vertex 1's coordinate row is missing.
    let s = b.simplex(cx, &[0, 1]);
    let e = b.ext(s, &[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    assert!(evc(e, 1, p, pr, s, &b).is_err());
}

/// An out-of-range membership row corresponds to no model state.
#[test]
fn refusal_out_of_range_membership() {
    let mut b = Body::new();
    let cx = b.line_complex(&[(1, 1), (2, 1)]);
    let s = b.simplex(cx, &[0, 1, 5]);
    let e = b.ext(s, &[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    assert!(evc(e, 1, p, pr, s, &b).is_err());
}

/// Ambiguous formula constructor rows refuse (never pick).
#[test]
fn refusal_ambiguous_predicate_ctor() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    b.ctor_at("FTrue", vec![], pr);
    assert!(evc(e, 1, p, pr, s, &b).is_err());
}

/// A wild degree literal refuses at the budget, never enumerates.
#[test]
fn refusal_degree_past_the_budget() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    assert!(evc(e, 1 << 40, p, pr, s, &b).is_err());
}

// ---------------------------------------------------------------------
// Golden anchors — the subdivision cover (EvalDemo.lean's coverCheck
// receipts, each a kernel-checked verdict)
// ---------------------------------------------------------------------

/// The cover cast: B = [1, 2]; branch pairs as given (each branch a
/// fresh two-vertex complex). Returns (B simplex, B ext, node,
/// certificate term, x term).
fn cover_cast(
    b: &mut Body,
    parent_ext: &[u64],
    branches: &[&[(i64, u64)]],
) -> (u32, u32, u32, u32, u32) {
    let (s, e) = b.demo_b(parent_ext);
    let mut pairs = Vec::new();
    for coords in branches {
        let cx = b.line_complex(coords);
        let bs = b.simplex(cx, &[0, 1]);
        let be = b.ext(bs, &[]);
        pairs.push((bs, be));
    }
    let p = b.subdivide(&pairs);
    let cert = b.tconst((0, 1));
    let x = b.tconst((0, 1));
    (s, e, p, cert, x)
}

/// `coverCheck simplexB Sempty 2 [L, R] = true`: [1, 3/2] ∪ [3/2, 2]
/// covers [1, 2].
#[test]
fn cover_two_halves_hold() {
    let mut b = Body::new();
    let (s, e, p, cert, x) = cover_cast(&mut b, &[], &[&[(1, 1), (3, 2)], &[(3, 2), (2, 1)]]);
    assert_eq!(evv(e, cert, p, s, x, &b), Ok(true));
}

/// `coverCheck … [G, R] = false`: the gap (4/3, 3/2) is uncovered.
#[test]
fn cover_gap_fails() {
    let mut b = Body::new();
    let (s, e, p, cert, x) = cover_cast(&mut b, &[], &[&[(1, 1), (4, 3)], &[(3, 2), (2, 1)]]);
    assert_eq!(evv(e, cert, p, s, x, &b), Ok(false));
}

/// A single-vertex branch has no interval reading — decided false
/// (the demo's `simplexPt` case).
#[test]
fn cover_point_branch_fails() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let cx = b.line_complex(&[(1, 1), (2, 1)]);
    let bs = b.simplex(cx, &[0]);
    let be = b.ext(bs, &[]);
    let p = b.subdivide(&[(bs, be)]);
    let cert = b.tconst((0, 1));
    let x = b.tconst((0, 1));
    assert_eq!(evv(e, cert, p, s, x, &b), Ok(false));
}

/// A nonempty parent extension mask has no interval reading — decided
/// false (the demo's `SextB` case).
#[test]
fn cover_nonempty_parent_extension_fails() {
    let mut b = Body::new();
    let (s, e, p, cert, x) = cover_cast(&mut b, &[0], &[&[(1, 1), (3, 2)], &[(3, 2), (2, 1)]]);
    assert_eq!(evv(e, cert, p, s, x, &b), Ok(false));
}

/// Branch order does not matter: the chain re-passes (`nBranches`
/// extension passes), so [R, L] still covers.
#[test]
fn cover_reversed_order_holds() {
    let mut b = Body::new();
    let (s, e, p, cert, x) = cover_cast(&mut b, &[], &[&[(3, 2), (2, 1)], &[(1, 1), (3, 2)]]);
    assert_eq!(evv(e, cert, p, s, x, &b), Ok(true));
}

/// A single branch may exceed the parent: [0, 3] covers [1, 2].
#[test]
fn cover_oversized_branch_holds() {
    let mut b = Body::new();
    let (s, e, p, cert, x) = cover_cast(&mut b, &[], &[&[(0, 1), (3, 1)]]);
    assert_eq!(evv(e, cert, p, s, x, &b), Ok(true));
}

/// A degenerate branch (coincident vertex coordinates) has no
/// interval reading — decided false.
#[test]
fn cover_degenerate_branch_fails() {
    let mut b = Body::new();
    let (s, e, p, cert, x) = cover_cast(&mut b, &[], &[&[(1, 1), (1, 1)]]);
    assert_eq!(evv(e, cert, p, s, x, &b), Ok(false));
}

/// Zero branches never cover a nondegenerate interval.
#[test]
fn cover_zero_branches_fails() {
    let mut b = Body::new();
    let (s, e, p, cert, x) = cover_cast(&mut b, &[], &[]);
    assert_eq!(evv(e, cert, p, s, x, &b), Ok(false));
}

/// The demo's branch-swap golden (`branchS(k).simplex ≠
/// branchSimplex(k)`) transposes to a REFUSAL at row grain (module
/// adjudication: chase congruence is not in view; the Lean's decided
/// false is undecidable over distinct elements).
#[test]
fn cover_branch_simplex_mismatch_refuses() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let cx_l = b.line_complex(&[(1, 1), (3, 2)]);
    let bs_l = b.simplex(cx_l, &[0, 1]);
    let be_l = b.ext(bs_l, &[]);
    let cx_r = b.line_complex(&[(3, 2), (2, 1)]);
    let bs_r = b.simplex(cx_r, &[0, 1]);
    let be_r = b.ext(bs_r, &[]);
    // branchSimplex[0] = R's simplex, but branchS[0] = L's extension.
    let p = b.subdivide(&[(bs_r, be_l), (bs_l, be_r)]);
    let cert = b.tconst((0, 1));
    let x = b.tconst((0, 1));
    let err = evv(e, cert, p, s, x, &b).expect_err("refuses");
    assert!(err.contains("row-grain distinct"), "{err}");
}

// ---------------------------------------------------------------------
// Cover mutants + refusals
// ---------------------------------------------------------------------

/// The near-cover mutant: shrink R's left endpoint past L's right —
/// [1, 3/2] ∪ [8/5, 2] leaves (3/2, 8/5) uncovered.
#[test]
fn mutant_cover_epsilon_gap_fails() {
    let mut b = Body::new();
    let (s, e, p, cert, x) = cover_cast(&mut b, &[], &[&[(1, 1), (3, 2)], &[(8, 5), (2, 1)]]);
    assert_eq!(evv(e, cert, p, s, x, &b), Ok(false));
}

/// The parent-widening mutant: the same branches fail a widened
/// parent [1, 3].
#[test]
fn mutant_cover_widened_parent_fails() {
    let mut b = Body::new();
    let cx = b.line_complex(&[(1, 1), (3, 1)]);
    let s = b.simplex(cx, &[0, 1]);
    let e = b.ext(s, &[]);
    let cx_l = b.line_complex(&[(1, 1), (3, 2)]);
    let bs_l = b.simplex(cx_l, &[0, 1]);
    let be_l = b.ext(bs_l, &[]);
    let cx_r = b.line_complex(&[(3, 2), (2, 1)]);
    let bs_r = b.simplex(cx_r, &[0, 1]);
    let be_r = b.ext(bs_r, &[]);
    let p = b.subdivide(&[(bs_l, be_l), (bs_r, be_r)]);
    let cert = b.tconst((0, 1));
    let x = b.tconst((0, 1));
    assert_eq!(evv(e, cert, p, s, x, &b), Ok(false));
}

/// A gap in the branch family refuses (the model's branch functions
/// are total on `Fin nBranches`).
#[test]
fn refusal_cover_family_gap() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let cx_l = b.line_complex(&[(1, 1), (3, 2)]);
    let bs_l = b.simplex(cx_l, &[0, 1]);
    let be_l = b.ext(bs_l, &[]);
    let p = b.fresh();
    b.field("PSubdivide/nBranches", p, natv(2));
    b.branch_row("PSubdivide/branchSimplex", 0, p, lref(bs_l));
    b.branch_row("PSubdivide/branchS", 0, p, lref(be_l));
    // index 1 missing from both families.
    let cert = b.tconst((0, 1));
    let x = b.tconst((0, 1));
    assert!(evv(e, cert, p, s, x, &b).is_err());
}

/// A duplicate branch index refuses.
#[test]
fn refusal_cover_duplicate_index() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let cx_l = b.line_complex(&[(1, 1), (3, 2)]);
    let bs_l = b.simplex(cx_l, &[0, 1]);
    let be_l = b.ext(bs_l, &[]);
    let p = b.fresh();
    b.field("PSubdivide/nBranches", p, natv(1));
    b.branch_row("PSubdivide/branchSimplex", 0, p, lref(bs_l));
    b.branch_row("PSubdivide/branchSimplex", 0, p, lref(bs_l));
    b.branch_row("PSubdivide/branchS", 0, p, lref(be_l));
    let cert = b.tconst((0, 1));
    let x = b.tconst((0, 1));
    assert!(evv(e, cert, p, s, x, &b).is_err());
}

/// An out-of-range branch index refuses.
#[test]
fn refusal_cover_index_past_count() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let cx_l = b.line_complex(&[(1, 1), (3, 2)]);
    let bs_l = b.simplex(cx_l, &[0, 1]);
    let be_l = b.ext(bs_l, &[]);
    let p = b.fresh();
    b.field("PSubdivide/nBranches", p, natv(1));
    b.branch_row("PSubdivide/branchSimplex", 0, p, lref(bs_l));
    b.branch_row("PSubdivide/branchS", 0, p, lref(be_l));
    b.branch_row("PSubdivide/branchSimplex", 5, p, lref(bs_l));
    let cert = b.tconst((0, 1));
    let x = b.tconst((0, 1));
    assert!(evv(e, cert, p, s, x, &b).is_err());
}

/// A missing branch-count row refuses (structure not in view).
#[test]
fn refusal_cover_missing_branch_count() {
    let mut b = Body::new();
    let (s, e) = b.demo_b(&[]);
    let p = b.fresh();
    let cert = b.tconst((0, 1));
    let x = b.tconst((0, 1));
    assert!(evv(e, cert, p, s, x, &b).is_err());
}

/// A literal in the carried-term positions is a malformed cell —
/// refused at the argument boundary (the term itself is never read).
#[test]
fn refusal_cover_literal_carried_term() {
    let mut b = Body::new();
    let (s, e, p, _cert, x) = cover_cast(&mut b, &[], &[&[(1, 1), (2, 1)]]);
    let args = [lref(e), natv(9), lref(p), lref(s), lref(x)];
    let refs: Vec<&Value> = args.iter().collect();
    assert!(common::ev("coverInfeasibilityValid", &refs, &b.rows()).is_err());
}

/// The carried terms may be EXTERNAL element refs: their structure is
/// never read (the Lean signature ignores them), so the single-body
/// rule does not bind them.
#[test]
fn cover_external_carried_terms_hold() {
    let mut b = Body::new();
    let (s, e, p, _cert, _x) = cover_cast(&mut b, &[], &[&[(0, 1), (3, 1)]]);
    let ext_term = Value::Ref(ElemRef::External {
        dep_index: 0,
        counter: 700,
    });
    let args = [
        lref(e),
        ext_term.clone(),
        lref(p),
        lref(s),
        ext_term.clone(),
    ];
    let refs: Vec<&Value> = args.iter().collect();
    assert_eq!(
        common::ev("coverInfeasibilityValid", &refs, &b.rows()),
        Ok(true)
    );
}

// ---------------------------------------------------------------------
// The frozen cross-implementation corpus (python `fractions` arm — an
// independent transcription of the Lean checkers, verdicts DERIVED by
// running it, never asserted): replay every instance through provider
// dispatch and require verdict agreement. Disagreement =
// stop-and-investigate, never adjust-the-corpus.
// ---------------------------------------------------------------------

#[test]
fn pyref_corpus_replays() {
    use serde_json::Value as J;
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/berncone_pyref_corpus.json"
    );
    let corpus: J = serde_json::from_str(&std::fs::read_to_string(path).expect("corpus present"))
        .expect("corpus parses");

    fn qp(j: &J) -> (i64, u64) {
        let a = j.as_array().expect("q pair");
        (a[0].as_i64().expect("num"), a[1].as_u64().expect("den"))
    }

    /// Build a geometry record: (simplex, ext).
    fn build_geom(b: &mut Body, j: &J) -> (u32, u32) {
        let amb = j["amb"].as_u64().expect("amb");
        let coords = j["coords"].as_array().expect("coords");
        let cx = b.fresh();
        b.field("SimpC/n_vertices", cx, natv(coords.len() as u64));
        b.field("SimpC/amb_dim", cx, natv(amb));
        for (v, row) in coords.iter().enumerate() {
            for (jj, q) in row.as_array().expect("vertex row").iter().enumerate() {
                let (num, den) = qp(q);
                b.coord(cx, v as u64, jj as u64, num, den);
            }
        }
        let sverts: Vec<u64> = j["sverts"]
            .as_array()
            .expect("sverts")
            .iter()
            .map(|v| v.as_u64().expect("vert"))
            .collect();
        let everts: Vec<u64> = j["everts"]
            .as_array()
            .expect("everts")
            .iter()
            .map(|v| v.as_u64().expect("vert"))
            .collect();
        let s = b.simplex(cx, &sverts);
        let e = b.ext(s, &everts);
        (s, e)
    }

    fn build_term(b: &mut Body, j: &J, pool: &[Value]) -> u32 {
        let a = j.as_array().expect("term node");
        match a[0].as_str().expect("tag") {
            "var" => {
                let w = pool[a[1].as_u64().expect("wire index") as usize].clone();
                b.tvar(&w)
            }
            "const" => b.tconst(qp(&a[1])),
            "hole" => b.thole(),
            "neg" => {
                let t = build_term(b, &a[1], pool);
                b.ctor("TNeg", vec![lref(t)])
            }
            "idx" => {
                let t = build_term(b, &a[1], pool);
                b.tidx(t, a[2].as_u64().expect("idx"))
            }
            op @ ("add" | "mul" | "sub") => {
                let l = build_term(b, &a[1], pool);
                let r = build_term(b, &a[2], pool);
                match op {
                    "add" => b.tadd(l, r),
                    "mul" => b.tmul(l, r),
                    _ => b.ctor("TSub", vec![lref(l), lref(r)]),
                }
            }
            other => panic!("unexpected term tag {other}"),
        }
    }

    fn build_pred(b: &mut Body, j: &J, pool: &[Value]) -> u32 {
        let a = j.as_array().expect("formula node");
        match a[0].as_str().expect("tag") {
            "and" | "or" => {
                let l = build_pred(b, &a[1], pool);
                let r = build_pred(b, &a[2], pool);
                if a[0] == "and" {
                    b.fand(l, r)
                } else {
                    b.f_or(l, r)
                }
            }
            "atom" => {
                let op = match a[1].as_str().expect("cmp") {
                    "lt" => "FAtomLT",
                    "le" => "FAtomLE",
                    "eq" => "FAtomEQ",
                    "ge" => "FAtomGE",
                    "gt" => "FAtomGT",
                    "ne" => "FAtomNE",
                    other => panic!("unexpected cmp {other}"),
                };
                let l = build_term(b, &a[2], pool);
                let r = build_term(b, &a[3], pool);
                b.fatom(op, l, r)
            }
            "true" => b.ftrue(),
            "false" => b.ctor("FFalse", vec![]),
            "sph" => b.ctor("FSpH", vec![]),
            other => panic!("unexpected formula tag {other}"),
        }
    }

    let mut counts: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut verdicts = [0usize; 2];

    for (i, case) in corpus["coeffs"]
        .as_array()
        .expect("coeffs cases")
        .iter()
        .enumerate()
    {
        let kind = case["kind"].as_str().expect("kind");
        let verdict = case["verdict"].as_bool().expect("verdict");
        let mut b = Body::new();
        let pool: Vec<Value> = (0..3).map(|_| lref(b.fresh())).collect();
        let (s, e) = build_geom(&mut b, &case["geom"]);
        let poly = build_term(&mut b, &case["poly"], &pool);
        let pred = build_pred(&mut b, &case["pred"], &pool);
        let degree = case["degree"].as_u64().expect("degree");
        let got = evc(e, degree, poly, pred, s, &b);
        assert_eq!(
            got,
            Ok(verdict),
            "coeffs corpus case {i} ({kind}) disagrees with the python arm"
        );
        *counts.entry(format!("coeffs/{kind}")).or_default() += 1;
        verdicts[usize::from(verdict)] += 1;
    }

    for (i, case) in corpus["cover"]
        .as_array()
        .expect("cover cases")
        .iter()
        .enumerate()
    {
        let kind = case["kind"].as_str().expect("kind");
        let verdict = case["verdict"].as_bool().expect("verdict");
        let mut b = Body::new();
        let (s, e) = build_geom(&mut b, &case["parent"]);
        let mut pairs = Vec::new();
        for br in case["branches"].as_array().expect("branches") {
            pairs.push(build_geom(&mut b, br));
        }
        let p = b.subdivide(&pairs);
        let cert = b.tconst((0, 1));
        let x = b.tconst((0, 1));
        let got = evv(e, cert, p, s, x, &b);
        assert_eq!(
            got,
            Ok(verdict),
            "cover corpus case {i} ({kind}) disagrees with the python arm"
        );
        *counts.entry(format!("cover/{kind}")).or_default() += 1;
        verdicts[usize::from(verdict)] += 1;
    }

    let total: usize = counts.values().sum();
    assert!(total >= 200, "corpus size: {counts:?}");
    assert!(
        verdicts[0] >= 60 && verdicts[1] >= 60,
        "both verdicts well represented: {verdicts:?}"
    );
}
