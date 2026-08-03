//! The Bernstein-cone float lane exercised end to end through
//! provider dispatch: `allForwardDiffBernIntvEnclosuresSatisfyP` —
//! the forward-difference grid recomputed in validated dtype-interval
//! arithmetic, P checked at the interval lower endpoints — see the
//! module docs in `src/berncone.rs` — the false verdict gated on the
//! certified upward-closed-conic classification.
//!
//! Golden anchors: the exact twin's demo-by-hand geometry (branch B
//! `[1, 2]`, grid `{5/2, 9/2}`) — on all-dyadic inputs the interval
//! pipeline stays zero-width, so the float lane must agree with the
//! exact lane exactly; engineered nondyadic straddles pin the REFUSE
//! frontier; the format-range cases pin the ∞-routing arms. Claim
//! order is the declaring theory's bytewise field order (S, degree,
//! dtype, polynomial, predicate, simplex) — enforced in production by
//! the binder's signature adjudication against the staged
//! declaration, which no synthetic fixture can stand in for.
//!
//! The test-side row emitter shares no code with the evaluators.

mod common;

use common::{stack, STACK};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;

const OWN: [u8; 32] = [0xBD; 32];

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

    fn line_complex(&mut self, coords: &[(i64, u64)]) -> u32 {
        let c = self.fresh();
        self.field("SimpC/n_vertices", c, natv(coords.len() as u64));
        self.field("SimpC/amb_dim", c, natv(1));
        for (v, (num, den)) in coords.iter().enumerate() {
            self.coord(c, v as u64, 0, *num, *den);
        }
        c
    }

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

    /// The affine polynomial `c + s·x` over a wire.
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

    // ---- Dtype rows -------------------------------------------------

    fn konst(&mut self, name: &str) -> u32 {
        self.ctor(name, vec![])
    }

    /// A dtype via the `mkDtype` producer route.
    fn dtype_mk(&mut self, k: &str, s: &str, x: &str) -> u32 {
        let ke = self.konst(k);
        let se = self.konst(s);
        let xe = self.konst(x);
        self.ctor("mkDtype", vec![lref(ke), lref(se), lref(xe)])
    }

    /// A dtype via the alias route (`F64`, `Q`, …).
    fn dtype_alias(&mut self, name: &str) -> u32 {
        self.konst(name)
    }

    /// A dtype via direct axis field rows.
    fn dtype_fields(&mut self, k: &str, s: &str, x: &str) -> u32 {
        let ke = self.konst(k);
        let se = self.konst(s);
        let xe = self.konst(x);
        let d = self.fresh();
        self.field("Dtype/kind", d, lref(ke));
        self.field("Dtype/sign", d, lref(se));
        self.field("Dtype/ext", d, lref(xe));
        d
    }

    fn dtype_f64(&mut self) -> u32 {
        self.dtype_mk("KF64", "Ss", "Eext")
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

/// Dispatch with the registry's bytewise claim order: S, degree,
/// dtype, polynomial, predicate, simplex.
fn evi(
    s_ext: u32,
    degree: u64,
    dtype: u32,
    polynomial: u32,
    predicate: u32,
    simplex: u32,
    b: &Body,
) -> Result<bool, String> {
    let args = [
        lref(s_ext),
        natv(degree),
        lref(dtype),
        lref(polynomial),
        lref(predicate),
        lref(simplex),
    ];
    let refs: Vec<&Value> = args.iter().collect();
    common::ev("allForwardDiffBernIntvEnclosuresSatisfyP", &refs, &b.rows())
}

// ---------------------------------------------------------------------
// Goldens: dyadic inputs keep the pipeline zero-width — the float lane
// must agree with the exact lane exactly.
// ---------------------------------------------------------------------

/// Demo branch B: p = 1/2 + 2x on [1, 2], S = ∅, degree 1 — grid
/// exactly {5/2, 9/2}; P = (hole ≥ 0) holds at the lower endpoints.
#[test]
fn holds_demo_exact_dyadic() {
    let mut b = Body::new();
    let cx = b.line_complex(&[(1, 1), (2, 1)]);
    let s = b.simplex(cx, &[0, 1]);
    let e = b.ext(s, &[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    let d = b.dtype_f64();
    assert_eq!(evi(e, 1, d, p, pr, s, &b), Ok(true));
}

/// The same geometry through the alias and field dtype routes.
#[test]
fn holds_alias_and_field_dtype_routes() {
    for route in 0..2u8 {
        let mut b = Body::new();
        let cx = b.line_complex(&[(1, 1), (2, 1)]);
        let s = b.simplex(cx, &[0, 1]);
        let e = b.ext(s, &[]);
        let w = lref(b.fresh());
        let p = b.affine_wire_poly((1, 2), (2, 1), &w);
        let pr = b.pred("FAtomGE", (0, 1));
        let d = if route == 0 {
            b.dtype_alias("F64")
        } else {
            b.dtype_fields("KF32", "Ss", "Efin")
        };
        assert_eq!(evi(e, 1, d, p, pr, s, &b), Ok(true), "route {route}");
    }
}

/// The extension-mask path (S = {0} on the demo line): dyadic
/// forward-difference grid, exact agreement with the exact twin's
/// semantics (the fd combinatorics ride the same code shape).
#[test]
fn holds_extension_mask_dyadic() {
    let mut b = Body::new();
    let cx = b.line_complex(&[(1, 1), (2, 1)]);
    let s = b.simplex(cx, &[0, 1]);
    let e = b.ext(s, &[0]);
    let w = lref(b.fresh());
    // p = 2x: on the apex direction the forward differences stay
    // nonneg — transposed from the exact battery's mask cases.
    let p = b.affine_wire_poly((0, 1), (2, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    let d = b.dtype_f64();
    assert_eq!(evi(e, 1, d, p, pr, s, &b), Ok(true));
}

/// Nondyadic input with margin: p ≡ 1/10, P = (hole ≥ 0) — the
/// enclosure of 1/10 is one ulp wide at every format, entirely above
/// zero; holds at f64 AND at f16.
#[test]
fn holds_nondyadic_margin() {
    for (k, deg) in [("KF64", 1u64), ("KF16", 1u64)] {
        let mut b = Body::new();
        let cx = b.line_complex(&[(1, 1), (2, 1)]);
        let s = b.simplex(cx, &[0, 1]);
        let e = b.ext(s, &[]);
        let p = b.tconst((1, 10));
        let pr = b.pred("FAtomGE", (0, 1));
        let d = b.dtype_mk(k, "Ss", "Eext");
        assert_eq!(evi(e, deg, d, p, pr, s, &b), Ok(true), "kind {k}");
    }
}

// ---------------------------------------------------------------------
// The false arm.
// ---------------------------------------------------------------------

/// All-negative coefficients under a certified upward-closed-conic
/// predicate: p = −1 − x on [1, 2] (grid {−2, −3}), P = (hole ≥ 0):
/// every finite upper endpoint refutes P — decided false.
#[test]
fn false_negative_coeffs_gated() {
    let mut b = Body::new();
    let cx = b.line_complex(&[(1, 1), (2, 1)]);
    let s = b.simplex(cx, &[0, 1]);
    let e = b.ext(s, &[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((-1, 1), (-1, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    let d = b.dtype_f64();
    assert_eq!(evi(e, 1, d, p, pr, s, &b), Ok(false));
}

/// A structurally unevaluable predicate (`FInRegion` on an evaluated
/// path): `evalClosed` none-ness is hole-value-independent, so one
/// `none` refutes P(v) for every candidate witness — decided false
/// (the exact twin's posture, transposed).
#[test]
fn false_unevaluable_predicate() {
    let mut b = Body::new();
    let cx = b.line_complex(&[(1, 1), (2, 1)]);
    let s = b.simplex(cx, &[0, 1]);
    let e = b.ext(s, &[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let t = b.tconst((0, 1));
    let pr = b.ctor("FInRegion", vec![lref(e), lref(s), lref(t)]);
    let d = b.dtype_f64();
    assert_eq!(evi(e, 1, d, p, pr, s, &b), Ok(false));
}

/// Below the f16 finite range: p ≡ −100000 — the lower endpoint
/// routes to −∞ (never the finite clamp), the upper endpoint is the
/// directed-valid −maxFin = −65504, and P = (hole ≥ 0) refutes there:
/// decided false through the ∞-routing arm.
#[test]
fn false_below_range_f16() {
    let mut b = Body::new();
    let cx = b.line_complex(&[(1, 1), (2, 1)]);
    let s = b.simplex(cx, &[0, 1]);
    let e = b.ext(s, &[]);
    let p = b.tconst((-100000, 1));
    let pr = b.pred("FAtomGE", (0, 1));
    let d = b.dtype_mk("KF16", "Ss", "Eext");
    assert_eq!(evi(e, 1, d, p, pr, s, &b), Ok(false));
}

/// A certain degree lie (dyadic, interval excludes zero): x² claimed
/// at degree 1 — decided false, exactly as the exact twin.
#[test]
fn false_degree_lie_certain() {
    let mut b = Body::new();
    let cx = b.line_complex(&[(1, 1), (2, 1)]);
    let s = b.simplex(cx, &[0, 1]);
    let e = b.ext(s, &[]);
    let w = lref(b.fresh());
    let x = b.tvar(&w);
    let x2 = {
        let x_again = b.tvar(&w);
        b.tmul(x, x_again)
    };
    let pr = b.pred("FAtomGE", (0, 1));
    let d = b.dtype_f64();
    assert_eq!(evi(e, 1, d, x2, pr, s, &b), Ok(false));
}

/// Full-dimensionality gate transposed: three vertices on a 1-D
/// complex — decided false (structural arm, the exact twin's
/// semantics).
#[test]
fn false_dimensionality() {
    let mut b = Body::new();
    let cx = b.line_complex(&[(0, 1), (1, 1), (2, 1)]);
    let s = b.simplex(cx, &[0, 1, 2]);
    let e = b.ext(s, &[]);
    let p = b.tconst((1, 1));
    let pr = b.pred("FAtomGE", (0, 1));
    let d = b.dtype_f64();
    assert_eq!(evi(e, 1, d, p, pr, s, &b), Ok(false));
}

// ---------------------------------------------------------------------
// The refuse frontier.
// ---------------------------------------------------------------------

fn expect_refusal(r: Result<bool, String>, needle: &str, ctx: &str) {
    match r {
        Err(reason) => assert!(
            reason.contains(needle),
            "{ctx}: refusal reason should mention `{needle}`, got: {reason}"
        ),
        Ok(v) => panic!("{ctx}: expected refusal, got verdict {v}"),
    }
}

/// The engineered straddle: vertex at 1/3 with p = 3x − 1 — the grid
/// coefficient at that vertex is exactly 0, computed through
/// nondyadic enclosures that straddle it; P = (hole ≥ 0) neither
/// holds at the lower endpoint nor refutes at the upper — refused
/// (indeterminate at dtype width), at every float format.
#[test]
fn refuse_straddle_zero() {
    for k in ["KF64", "KF32", "KF16", "KF16bf"] {
        let mut b = Body::new();
        let cx = b.line_complex(&[(1, 3), (1, 1)]);
        let s = b.simplex(cx, &[0, 1]);
        let e = b.ext(s, &[]);
        let w = lref(b.fresh());
        let p = b.affine_wire_poly((-1, 1), (3, 1), &w);
        let pr = b.pred("FAtomGE", (0, 1));
        let d = b.dtype_mk(k, "Ss", "Eext");
        expect_refusal(
            evi(e, 1, d, p, pr, s, &b),
            "indeterminate at dtype width",
            &format!("straddle at {k}"),
        );
    }
}

/// The gate half of the trichotomy: p = 1 + x on [1, 2] (grid
/// {2, 3}), P = (hole ≥ 3) — the lower endpoints fail, an upper
/// endpoint refutes, but (hole ≥ 3) is NOT conic (nonzero constant),
/// so our false verdict is not licensed — refused.
#[test]
fn refuse_false_needs_upward_closed_gate() {
    let mut b = Body::new();
    let cx = b.line_complex(&[(1, 1), (2, 1)]);
    let s = b.simplex(cx, &[0, 1]);
    let e = b.ext(s, &[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 1), (1, 1), &w);
    let pr = b.pred("FAtomGE", (3, 1));
    let d = b.dtype_f64();
    expect_refusal(
        evi(e, 1, d, p, pr, s, &b),
        "indeterminate at dtype width",
        "nonconic gate",
    );
}

/// Below range under a non-upward-closed predicate: p ≡ −100000 at
/// f16 with P = (hole ≤ 0). The −∞ lower endpoint can witness
/// nothing, and LE is not upward-closed, so no verdict is available —
/// refused. (The mutant that clamps −∞ to −maxFin would accept here:
/// P(−65504) is true — the ∞-routing arm's kill witness.)
#[test]
fn refuse_le_below_range_f16() {
    let mut b = Body::new();
    let cx = b.line_complex(&[(1, 1), (2, 1)]);
    let s = b.simplex(cx, &[0, 1]);
    let e = b.ext(s, &[]);
    let p = b.tconst((-100000, 1));
    let pr = b.pred("FAtomLE", (0, 1));
    let d = b.dtype_mk("KF16", "Ss", "Eext");
    expect_refusal(
        evi(e, 1, d, p, pr, s, &b),
        "indeterminate at dtype width",
        "le below range",
    );
}

/// The straddling degree lie: p = x₀x₁ − 3x₀² over vertices
/// (1/3, 1), (1, 3), (0, 0) at degree 1 — every too-high monomial of
/// the parametrized polynomial either cancels exactly (dropped) or
/// straddles zero through nondyadic enclosures, so the lie is
/// indeterminate at dtype width — refused, never guessed.
#[test]
fn refuse_degree_lie_straddle() {
    let mut b = Body::new();
    let cx = b.nd_complex(
        2,
        &[&[(1, 3), (1, 1)], &[(1, 1), (3, 1)], &[(0, 1), (0, 1)]],
    );
    let s = b.simplex(cx, &[0, 1, 2]);
    let e = b.ext(s, &[]);
    let w = lref(b.fresh());
    let x0 = {
        let v = b.tvar(&w);
        b.tidx(v, 0)
    };
    let x1 = {
        let v = b.tvar(&w);
        b.tidx(v, 1)
    };
    let m01 = b.tmul(x0, x1);
    let x0b = {
        let v = b.tvar(&w);
        b.tidx(v, 0)
    };
    let x0c = {
        let v = b.tvar(&w);
        b.tidx(v, 0)
    };
    let sq = b.tmul(x0b, x0c);
    let neg3 = b.tconst((-3, 1));
    let scaled = b.tmul(neg3, sq);
    let p = b.tadd(m01, scaled);
    let pr = b.pred("FAtomGE", (0, 1));
    let d = b.dtype_f64();
    expect_refusal(
        evi(e, 1, d, p, pr, s, &b),
        "degree-lie indeterminate",
        "straddling lie",
    );
}

// ---------------------------------------------------------------------
// Dtype refusals.
// ---------------------------------------------------------------------

fn demo_geometry(b: &mut Body) -> (u32, u32, u32, u32) {
    let cx = b.line_complex(&[(1, 1), (2, 1)]);
    let s = b.simplex(cx, &[0, 1]);
    let e = b.ext(s, &[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    (s, e, p, pr)
}

#[test]
fn refuse_exact_dtype_alias() {
    let mut b = Body::new();
    let (s, e, p, pr) = demo_geometry(&mut b);
    let d = b.dtype_alias("Q");
    expect_refusal(evi(e, 1, d, p, pr, s, &b), "float lane refuses", "alias Q");
}

#[test]
fn refuse_exact_dtype_kind() {
    let mut b = Body::new();
    let (s, e, p, pr) = demo_geometry(&mut b);
    let d = b.dtype_mk("KRat", "Ss", "Efin");
    expect_refusal(evi(e, 1, d, p, pr, s, &b), "float lane refuses", "KRat");
}

#[test]
fn refuse_nonneg_sign() {
    let mut b = Body::new();
    let (s, e, p, pr) = demo_geometry(&mut b);
    let d = b.dtype_mk("KF64", "Snn", "Eext");
    expect_refusal(evi(e, 1, d, p, pr, s, &b), "nonneg", "Snn");
}

#[test]
fn refuse_unconstructed_dtype() {
    let mut b = Body::new();
    let (s, e, p, pr) = demo_geometry(&mut b);
    // A fresh element with no producer and no field rows.
    let d = b.fresh();
    expect_refusal(evi(e, 1, d, p, pr, s, &b), "Dtype/kind", "unconstructed");
}

#[test]
fn refuse_ambiguous_dtype() {
    let mut b = Body::new();
    let (s, e, p, pr) = demo_geometry(&mut b);
    let k1 = b.konst("KF64");
    let s1 = b.konst("Ss");
    let x1 = b.konst("Eext");
    let k2 = b.konst("KF32");
    let d = b.ctor("mkDtype", vec![lref(k1), lref(s1), lref(x1)]);
    // A second, conflicting mkDtype row producing the SAME element.
    let mk = b.xref(s_fun("mkDtype"));
    b.ops.push(Op::Funa {
        fun: mk,
        args: vec![lref(k2), lref(s1), lref(x1)],
        value: lref(d),
    });
    expect_refusal(
        evi(e, 1, d, p, pr, s, &b),
        "ambiguous dtype",
        "two mkDtype rows",
    );
}

/// Ext axis is verdict-neutral: Efin and Eext bind identically.
#[test]
fn ext_axis_neutral() {
    for x in ["Efin", "Eext"] {
        let mut b = Body::new();
        let (s, e, p, pr) = demo_geometry(&mut b);
        let d = b.dtype_mk("KF64", "Ss", x);
        assert_eq!(evi(e, 1, d, p, pr, s, &b), Ok(true), "ext {x}");
    }
}

// ---------------------------------------------------------------------
// Row-grain guards (the exact twin's, transposed).
// ---------------------------------------------------------------------

#[test]
fn refuse_distinct_simplex_elements() {
    let mut b = Body::new();
    let cx = b.line_complex(&[(1, 1), (2, 1)]);
    let s1 = b.simplex(cx, &[0, 1]);
    let s2 = b.simplex(cx, &[0, 1]);
    let e = b.ext(s1, &[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let pr = b.pred("FAtomGE", (0, 1));
    let d = b.dtype_f64();
    expect_refusal(
        evi(e, 1, d, p, pr, s2, &b),
        "row-grain distinct",
        "distinct simplex elements",
    );
}

/// Conjunction predicates ride the same sweep: P = (hole ≥ 0) ∧
/// (hole ≥ 0) holds on the dyadic demo; the same conjunction with an
/// unevaluable arm decides false through the non-short-circuiting
/// monad.
#[test]
fn conjunction_predicates() {
    let mut b = Body::new();
    let cx = b.line_complex(&[(1, 1), (2, 1)]);
    let s = b.simplex(cx, &[0, 1]);
    let e = b.ext(s, &[]);
    let w = lref(b.fresh());
    let p = b.affine_wire_poly((1, 2), (2, 1), &w);
    let a1 = b.pred("FAtomGE", (0, 1));
    let a2 = b.pred("FAtomGE", (0, 1));
    let pr = b.fand(a1, a2);
    let d = b.dtype_f64();
    assert_eq!(evi(e, 1, d, p, pr, s, &b), Ok(true));

    let mut b2 = Body::new();
    let cx = b2.line_complex(&[(1, 1), (2, 1)]);
    let s = b2.simplex(cx, &[0, 1]);
    let e = b2.ext(s, &[]);
    let w = lref(b.fresh());
    let p = b2.affine_wire_poly((1, 2), (2, 1), &w);
    let a1 = b2.pred("FAtomGE", (0, 1));
    let t = b2.tconst((0, 1));
    let reg = b2.ctor("FInRegion", vec![lref(e), lref(s), lref(t)]);
    let pr = b2.fand(a1, reg);
    let d = b2.dtype_f64();
    assert_eq!(evi(e, 1, d, p, pr, s, &b2), Ok(false));
}

// ---------------------------------------------------------------------
// The frozen cross-implementation corpus (fixtures/
// bernintv_pyref_corpus.json — generated by bernintv_pyref_gen.py,
// an independent python arm implementing the Lean rounding maps and
// the interval pipeline over `fractions.Fraction`; verdicts DERIVED,
// never asserted).
// ---------------------------------------------------------------------

#[test]
fn frozen_pyref_corpus() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/bernintv_pyref_corpus.json"
    );
    let corpus: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(path).expect("corpus present"))
            .expect("corpus parses");
    let cases = corpus["cases"].as_array().expect("cases array");
    assert!(cases.len() >= 200, "corpus size");
    let mut verdicts = [0usize; 3];
    for (i, case) in cases.iter().enumerate() {
        let mut b = Body::new();
        let verts: Vec<(i64, u64)> = case["verts"]
            .as_array()
            .expect("verts")
            .iter()
            .map(|v| (v[0].as_i64().expect("num"), v[1].as_u64().expect("den")))
            .collect();
        let cx = b.line_complex(&verts);
        let s = b.simplex(cx, &[0, 1]);
        let e = b.ext(s, &[]);
        let w = lref(b.fresh());
        let c0 = (
            case["poly"]["c0"][0].as_i64().unwrap(),
            case["poly"]["c0"][1].as_u64().unwrap(),
        );
        let c1 = (
            case["poly"]["c1"][0].as_i64().unwrap(),
            case["poly"]["c1"][1].as_u64().unwrap(),
        );
        let p = b.affine_wire_poly(c0, c1, &w);
        let atoms = case["pred"].as_array().expect("pred atoms");
        let mut pr: Option<u32> = None;
        for a in atoms {
            let op = a["op"].as_str().expect("op");
            let c = (a["c"][0].as_i64().unwrap(), a["c"][1].as_u64().unwrap());
            let atom = b.pred(
                match op {
                    "GE" => "FAtomGE",
                    "LE" => "FAtomLE",
                    other => panic!("op {other}"),
                },
                c,
            );
            pr = Some(match pr {
                None => atom,
                Some(prev) => b.fand(prev, atom),
            });
        }
        let pr = pr.expect("nonempty pred");
        let kind = match case["dtype"].as_str().expect("dtype") {
            "F64" => "KF64",
            "F32" => "KF32",
            "F16" => "KF16",
            "BF16" => "KF16bf",
            other => panic!("dtype {other}"),
        };
        let d = b.dtype_mk(kind, "Ss", "Eext");
        let degree = case["degree"].as_u64().expect("degree");
        let got = evi(e, degree, d, p, pr, s, &b);
        let expected = case["verdict"].as_str().expect("verdict");
        let got_str = match &got {
            Ok(true) => "holds",
            Ok(false) => "false",
            Err(_) => "refused",
        };
        assert_eq!(got_str, expected, "case {i}: {case} → {got:?}");
        verdicts[match got_str {
            "holds" => 0,
            "false" => 1,
            _ => 2,
        }] += 1;
    }
    // All three verdict classes must be populated — a corpus that
    // never exercises an arm pins nothing about it.
    assert!(
        verdicts.iter().all(|&n| n > 0),
        "verdict classes populated: {verdicts:?}"
    );
}
