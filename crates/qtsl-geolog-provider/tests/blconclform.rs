//! `barycentricHalfspaceForm` exercised end to end through provider
//! dispatch: the barycentric-halfspace conjunction recomputed from
//! simplex vertex-table rows and compared structurally against
//! formula rows — spec battery (including the executable Lean demo's
//! worked case), named data mutants (every mutant flips a verdict),
//! decided-`false` shapes, and refusals.
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

const OWN: [u8; 32] = [0xB7; 32];

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
/// tables, simplexes and extension sets, and Term/Formula constructor
/// rows.
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

    /// One halfspace atom in the realized canonical form:
    /// `(s'·t [+ c']) <= 0`. `c = None` selects the zero-offset `Mul`
    /// layout.
    fn halfspace_atom(&mut self, s: (i64, u64), c: Option<(i64, u64)>, t: u32) -> u32 {
        let sc = self.tconst(s.0, s.1);
        let prod = self.tmul(sc, t);
        let lhs = match c {
            None => prod,
            Some((num, den)) => {
                let cc = self.tconst(num, den);
                self.tadd(prod, cc)
            }
        };
        let zero = self.tconst(0, 1);
        self.fatom("FAtomLE", lhs, zero)
    }

    /// The two-atom conjunction in vertex order.
    fn halfspace_form(
        &mut self,
        a0: ((i64, u64), Option<(i64, u64)>),
        a1: ((i64, u64), Option<(i64, u64)>),
        t: u32,
    ) -> u32 {
        let x = self.halfspace_atom(a0.0, a0.1, t);
        let y = self.halfspace_atom(a1.0, a1.1, t);
        self.fand(x, y)
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

/// Field order: S, formula, simplex, t.
fn ev(s_ext: u32, formula: u32, simplex: u32, t: u32, b: &Body) -> Result<bool, String> {
    common::ev_elems(
        "barycentricHalfspaceForm",
        &[s_ext, formula, simplex, t],
        &b.rows(),
    )
}

/// The Lean demo's geometry: two vertices at 1 and 2, the full
/// simplex, a term to bound.
fn demo(b: &mut Body) -> (u32, u32, u32) {
    let k = b.line_complex(&[(1, 1), (2, 1)]);
    let sx = b.simplex(k, &[0, 1]);
    let w = b.fresh();
    let t = b.tvar(w);
    (k, sx, t)
}

// ---------------------------------------------------------------------
// The executable Lean demo's worked case, transcribed: vertices at
// 1 and 2, S = ∅, expected form
//   (1·t + (−2) <= 0) ∧ ((−1)·t + 1 <= 0).
// ---------------------------------------------------------------------

#[test]
fn lean_demo_case_holds() {
    let mut b = Body::new();
    let (_k, sx, t) = demo(&mut b);
    let s = b.ext(sx, &[]);
    let f = b.halfspace_form(((1, 1), Some((-2, 1))), ((-1, 1), Some((1, 1))), t);
    assert_eq!(ev(s, f, sx, t, &b), Ok(true));
}

#[test]
fn extended_vertex_flips_its_atom() {
    // S = {0}: vertex 0's coordinate keeps the `+` orientation
    // (λ₀ <= 0), so its rescaled atom is (−1, 2); vertex 1 stays
    // negated at (−1, 1).
    let mut b = Body::new();
    let (_k, sx, t) = demo(&mut b);
    let s = b.ext(sx, &[0]);
    let f = b.halfspace_form(((-1, 1), Some((2, 1))), ((-1, 1), Some((1, 1))), t);
    assert_eq!(ev(s, f, sx, t, &b), Ok(true));
}

#[test]
fn zero_offset_takes_the_mul_layout() {
    // Vertices at 0 and 1: λ₁'s negation rescales to (−1, 0), whose
    // pinned layout is the bare product (no `TAdd`, no zero constant).
    let mut b = Body::new();
    let k = b.line_complex(&[(0, 1), (1, 1)]);
    let sx = b.simplex(k, &[0, 1]);
    let w = b.fresh();
    let t = b.tvar(w);
    let s = b.ext(sx, &[]);
    let f = b.halfspace_form(((1, 1), Some((-1, 1))), ((-1, 1), None), t);
    assert_eq!(ev(s, f, sx, t, &b), Ok(true));
}

#[test]
fn fractional_coordinates_rescale_to_coprime_integers() {
    // Vertices at 1 and 3/2 (the Lean demo's left half): den = 1/2,
    // raw pairs (−2, 3) and (2, −2) negate and rescale to (2, −3) and
    // (−1, 1) — the gcd division is observable in the second atom.
    let mut b = Body::new();
    let k = b.line_complex(&[(1, 1), (3, 2)]);
    let sx = b.simplex(k, &[0, 1]);
    let w = b.fresh();
    let t = b.tvar(w);
    let s = b.ext(sx, &[]);
    let f = b.halfspace_form(((2, 1), Some((-3, 1))), ((-1, 1), Some((1, 1))), t);
    assert_eq!(ev(s, f, sx, t, &b), Ok(true));
}

#[test]
fn compound_term_argument_compares_structurally() {
    // t = w + 1/2 as a term tree; the formula embeds a structurally
    // equal but non-interned copy.
    let mut b = Body::new();
    let (_k, sx, _unused) = demo(&mut b);
    let w = b.fresh();
    let v1 = b.tvar(w);
    let h1 = b.tconst(1, 2);
    let t = b.tadd(v1, h1);
    let v2 = b.tvar(w);
    let h2 = b.tconst(1, 2);
    let t_copy = b.tadd(v2, h2);
    let s = b.ext(sx, &[]);
    let f = b.halfspace_form(((1, 1), Some((-2, 1))), ((-1, 1), Some((1, 1))), t_copy);
    assert_eq!(ev(s, f, sx, t, &b), Ok(true));
}

// ---------------------------------------------------------------------
// Mutants: each one row (or one constant) away from the demo case,
// each flipping Holds to Fails.
// ---------------------------------------------------------------------

#[test]
fn mutant_swapped_arms_fails() {
    let mut b = Body::new();
    let (_k, sx, t) = demo(&mut b);
    let s = b.ext(sx, &[]);
    let f = b.halfspace_form(((-1, 1), Some((1, 1))), ((1, 1), Some((-2, 1))), t);
    assert_eq!(ev(s, f, sx, t, &b), Ok(false));
}

#[test]
fn mutant_wrong_constant_fails() {
    let mut b = Body::new();
    let (_k, sx, t) = demo(&mut b);
    let s = b.ext(sx, &[]);
    let f = b.halfspace_form(((1, 1), Some((2, 1))), ((-1, 1), Some((1, 1))), t);
    assert_eq!(ev(s, f, sx, t, &b), Ok(false));
}

#[test]
fn mutant_unscaled_multiple_fails() {
    // (2, −4) is the same halfspace as (1, −2) but not the positive
    // primitive-integer rescale — canonicality is part of the claim.
    let mut b = Body::new();
    let (_k, sx, t) = demo(&mut b);
    let s = b.ext(sx, &[]);
    let f = b.halfspace_form(((2, 1), Some((-4, 1))), ((-1, 1), Some((1, 1))), t);
    assert_eq!(ev(s, f, sx, t, &b), Ok(false));
}

#[test]
fn mutant_wrong_comparator_fails() {
    let mut b = Body::new();
    let (_k, sx, t) = demo(&mut b);
    let s = b.ext(sx, &[]);
    // First atom with GE instead of LE.
    let sc = b.tconst(1, 1);
    let prod = b.tmul(sc, t);
    let cc = b.tconst(-2, 1);
    let lhs = b.tadd(prod, cc);
    let zero = b.tconst(0, 1);
    let x = b.fatom("FAtomGE", lhs, zero);
    let y = b.halfspace_atom((-1, 1), Some((1, 1)), t);
    let f = b.fand(x, y);
    assert_eq!(ev(s, f, sx, t, &b), Ok(false));
}

#[test]
fn mutant_or_head_fails() {
    let mut b = Body::new();
    let (_k, sx, t) = demo(&mut b);
    let s = b.ext(sx, &[]);
    let x = b.halfspace_atom((1, 1), Some((-2, 1)), t);
    let y = b.halfspace_atom((-1, 1), Some((1, 1)), t);
    let f = b.ctor("FOr", vec![lref(x), lref(y)]);
    assert_eq!(ev(s, f, sx, t, &b), Ok(false));
}

#[test]
fn mutant_membership_row_flips_verdict() {
    // The demo formula is the S = ∅ rendering; adding the one
    // membership row that makes S = {0} must flip Holds to Fails.
    let mut b = Body::new();
    let (_k, sx, t) = demo(&mut b);
    let s = b.ext(sx, &[]);
    let f = b.halfspace_form(((1, 1), Some((-2, 1))), ((-1, 1), Some((1, 1))), t);
    assert_eq!(ev(s, f, sx, t, &b), Ok(true));
    b.member("ExtensionSet/contains", s, 0);
    assert_eq!(ev(s, f, sx, t, &b), Ok(false));
}

#[test]
fn mutant_wrong_term_fails() {
    // The formula is built over a DIFFERENT wire's variable: wires are
    // nominal, so the structural comparison decides false.
    let mut b = Body::new();
    let (_k, sx, t) = demo(&mut b);
    let w2 = b.fresh();
    let t2 = b.tvar(w2);
    let s = b.ext(sx, &[]);
    let f = b.halfspace_form(((1, 1), Some((-2, 1))), ((-1, 1), Some((1, 1))), t2);
    assert_eq!(ev(s, f, sx, t, &b), Ok(false));
}

#[test]
fn mutant_swapped_product_order_fails() {
    // t·s' instead of s'·t: the layout pins the constant on the left.
    let mut b = Body::new();
    let (_k, sx, t) = demo(&mut b);
    let s = b.ext(sx, &[]);
    let sc = b.tconst(1, 1);
    let prod = b.tmul(t, sc);
    let cc = b.tconst(-2, 1);
    let lhs = b.tadd(prod, cc);
    let zero = b.tconst(0, 1);
    let x = b.fatom("FAtomLE", lhs, zero);
    let y = b.halfspace_atom((-1, 1), Some((1, 1)), t);
    let f = b.fand(x, y);
    assert_eq!(ev(s, f, sx, t, &b), Ok(false));
}

#[test]
fn mutant_mul_layout_where_add_expected_fails() {
    // Dropping the nonzero offset (bare product where the rescaled
    // offset is −2) is a shape mismatch, decided false.
    let mut b = Body::new();
    let (_k, sx, t) = demo(&mut b);
    let s = b.ext(sx, &[]);
    let f = b.halfspace_form(((1, 1), None), ((-1, 1), Some((1, 1))), t);
    assert_eq!(ev(s, f, sx, t, &b), Ok(false));
}

// ---------------------------------------------------------------------
// The construction's `none` branches: decided `false` for every
// formula argument.
// ---------------------------------------------------------------------

fn any_form(b: &mut Body, t: u32) -> u32 {
    b.halfspace_form(((1, 1), Some((-2, 1))), ((-1, 1), Some((1, 1))), t)
}

#[test]
fn ambient_dimension_two_fails() {
    let mut b = Body::new();
    let k = b.fresh();
    b.field("SimpC/n_vertices", k, natv(2));
    b.field("SimpC/amb_dim", k, natv(2));
    for v in 0..2u64 {
        for j in 0..2u64 {
            b.coord(k, v, j, (v + j) as i64, 1);
        }
    }
    let sx = b.simplex(k, &[0, 1]);
    let w = b.fresh();
    let t = b.tvar(w);
    let s = b.ext(sx, &[]);
    let f = any_form(&mut b, t);
    assert_eq!(ev(s, f, sx, t, &b), Ok(false));
}

#[test]
fn wrong_vertex_counts_fail() {
    for verts in [&[0u64][..], &[0, 1, 2][..], &[][..]] {
        let mut b = Body::new();
        let k = b.line_complex(&[(0, 1), (1, 1), (2, 1)]);
        let sx = b.simplex(k, verts);
        let w = b.fresh();
        let t = b.tvar(w);
        let s = b.ext(sx, &[]);
        let f = any_form(&mut b, t);
        assert_eq!(
            ev(s, f, sx, t, &b),
            Ok(false),
            "vertex count {} must be a decided false",
            verts.len()
        );
    }
}

#[test]
fn coincident_coordinates_fail() {
    // The construction's defensive branch, mirrored verbatim
    // (unreachable for a genuine complex — module docs).
    let mut b = Body::new();
    let k = b.line_complex(&[(1, 1), (1, 1)]);
    let sx = b.simplex(k, &[0, 1]);
    let w = b.fresh();
    let t = b.tvar(w);
    let s = b.ext(sx, &[]);
    let f = any_form(&mut b, t);
    assert_eq!(ev(s, f, sx, t, &b), Ok(false));
}

// ---------------------------------------------------------------------
// Refusals (undecidable is never a verdict)
// ---------------------------------------------------------------------

#[test]
fn distinct_simplex_elements_refuse() {
    // The extension set rides a row-grain DISTINCT simplex element,
    // mask-identical to the argument: the same-simplex guard is
    // undecidable at row grain.
    let mut b = Body::new();
    let (k, sx, t) = demo(&mut b);
    let sx2 = b.simplex(k, &[0, 1]);
    let s = b.ext(sx2, &[]);
    let f = any_form(&mut b, t);
    let err = ev(s, f, sx, t, &b).unwrap_err();
    assert!(
        err.contains("row-grain distinct"),
        "distinct simplex elements must refuse: {err}"
    );
}

#[test]
fn missing_amb_dim_refuses() {
    let mut b = Body::new();
    let k = b.fresh();
    b.field("SimpC/n_vertices", k, natv(2));
    b.coord(k, 0, 0, 1, 1);
    b.coord(k, 1, 0, 2, 1);
    let sx = b.simplex(k, &[0, 1]);
    let w = b.fresh();
    let t = b.tvar(w);
    let s = b.ext(sx, &[]);
    let f = any_form(&mut b, t);
    let err = ev(s, f, sx, t, &b).unwrap_err();
    assert!(
        err.contains("no `SimpC/amb_dim` row"),
        "missing ambient dimension must refuse: {err}"
    );
}

#[test]
fn missing_coordinate_refuses() {
    let mut b = Body::new();
    let k = b.fresh();
    b.field("SimpC/n_vertices", k, natv(2));
    b.field("SimpC/amb_dim", k, natv(1));
    b.coord(k, 0, 0, 1, 1); // vertex 1's coordinate is absent
    let sx = b.simplex(k, &[0, 1]);
    let w = b.fresh();
    let t = b.tvar(w);
    let s = b.ext(sx, &[]);
    let f = any_form(&mut b, t);
    let err = ev(s, f, sx, t, &b).unwrap_err();
    assert!(
        err.contains("no `SimpC/coord` row for vertex 1"),
        "incomplete vertex table must refuse: {err}"
    );
}

#[test]
fn conflicting_coordinates_refuse() {
    let mut b = Body::new();
    let (k, sx, t) = demo(&mut b);
    b.coord(k, 0, 0, 5, 1); // conflicts with the demo's vertex 0 at 1
    let s = b.ext(sx, &[]);
    let f = any_form(&mut b, t);
    let err = ev(s, f, sx, t, &b).unwrap_err();
    assert!(
        err.contains("ambiguous `SimpC/coord`"),
        "conflicting coordinate rows must refuse: {err}"
    );
}

#[test]
fn out_of_range_coordinate_row_refuses() {
    let mut b = Body::new();
    let (k, sx, t) = demo(&mut b);
    b.coord(k, 7, 0, 1, 1); // 7 >= 2 vertices
    let s = b.ext(sx, &[]);
    let f = any_form(&mut b, t);
    let err = ev(s, f, sx, t, &b).unwrap_err();
    assert!(
        err.contains("at or past the complex's"),
        "out-of-range coordinate row must refuse: {err}"
    );
}

#[test]
fn out_of_range_axis_row_refuses() {
    let mut b = Body::new();
    let (k, sx, t) = demo(&mut b);
    b.coord(k, 0, 3, 1, 1); // axis 3 >= amb_dim 1
    let s = b.ext(sx, &[]);
    let f = any_form(&mut b, t);
    let err = ev(s, f, sx, t, &b).unwrap_err();
    assert!(
        err.contains("ambient dimension"),
        "out-of-range axis row must refuse: {err}"
    );
}

#[test]
fn out_of_range_extension_membership_refuses() {
    let mut b = Body::new();
    let (_k, sx, t) = demo(&mut b);
    let s = b.ext(sx, &[9]); // 9 >= 2 vertices
    let f = any_form(&mut b, t);
    let err = ev(s, f, sx, t, &b).unwrap_err();
    assert!(
        err.contains("at or past the complex's"),
        "out-of-range membership row must refuse: {err}"
    );
}

#[test]
fn unconstructed_formula_refuses() {
    let mut b = Body::new();
    let (_k, sx, t) = demo(&mut b);
    let s = b.ext(sx, &[]);
    let ghost = b.fresh(); // no constructor row
    let err = ev(s, ghost, sx, t, &b).unwrap_err();
    assert!(
        err.contains("no formula constructor row") || err.contains("structure undecidable"),
        "unconstructed formula must refuse: {err}"
    );
}

#[test]
fn non_q_coordinate_refuses() {
    let mut b = Body::new();
    let k = b.fresh();
    b.field("SimpC/n_vertices", k, natv(2));
    b.field("SimpC/amb_dim", k, natv(1));
    // Vertex 0's coordinate cell is a Nat, not a Q.
    b.ops.push(Op::Funa {
        fun: b.xref(s_fun("SimpC/coord")),
        args: vec![lref(k), natv(0), natv(0)],
        value: natv(1),
    });
    b.coord(k, 1, 0, 2, 1);
    let sx = b.simplex(k, &[0, 1]);
    let w = b.fresh();
    let t = b.tvar(w);
    let s = b.ext(sx, &[]);
    let f = any_form(&mut b, t);
    let err = ev(s, f, sx, t, &b).unwrap_err();
    assert!(
        err.contains("not a canonical Q literal"),
        "non-Q coordinate must refuse: {err}"
    );
}

#[test]
fn provider_claims_the_relation() {
    assert!(provider()
        .local_by_name("barycentricHalfspaceForm")
        .is_some());
}

// ---------------------------------------------------------------------
// The frozen cross-implementation corpus (python `fractions` arm —
// an independent transcription of the construction and its rescale):
// replay every instance through provider dispatch and require verdict
// agreement. Disagreement = stop-and-investigate, never
// adjust-the-corpus.
// ---------------------------------------------------------------------

#[test]
fn pyref_corpus_replays() {
    use serde_json::Value as J;
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/barycoord_pyref_corpus.json"
    );
    let corpus: J = serde_json::from_str(&std::fs::read_to_string(path).expect("corpus present"))
        .expect("corpus parses");
    let pair = |j: &J| -> (i64, u64) {
        let a = j.as_array().expect("num/den pair");
        (a[0].as_i64().expect("num"), a[1].as_u64().expect("den"))
    };
    let atom_spec = |j: &J| -> ((i64, u64), Option<(i64, u64)>) {
        let s = pair(&j["s"]);
        let c = if j["c"].is_null() {
            None
        } else {
            Some(pair(&j["c"]))
        };
        (s, c)
    };
    let mut counts: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    for (i, case) in corpus["cases"]
        .as_array()
        .expect("cases")
        .iter()
        .enumerate()
    {
        let kind = case["kind"].as_str().expect("kind");
        let coords: Vec<(i64, u64)> = case["coords"]
            .as_array()
            .expect("coords")
            .iter()
            .map(pair)
            .collect();
        let verts: Vec<u64> = case["simplex"]
            .as_array()
            .expect("simplex")
            .iter()
            .map(|v| v.as_u64().expect("vertex"))
            .collect();
        let ext: Vec<u64> = case["ext"]
            .as_array()
            .expect("ext")
            .iter()
            .map(|v| v.as_u64().expect("vertex"))
            .collect();
        let atoms = case["atoms"].as_array().expect("atoms");
        let (a0, a1) = (atom_spec(&atoms[0]), atom_spec(&atoms[1]));
        let verdict = case["verdict"].as_bool().expect("verdict");

        let mut b = Body::new();
        let k = b.line_complex(&coords);
        let sx = b.simplex(k, &verts);
        let w = b.fresh();
        let t = b.tvar(w);
        let s = b.ext(sx, &ext);
        let f = b.halfspace_form(a0, a1, t);
        assert_eq!(
            ev(s, f, sx, t, &b),
            Ok(verdict),
            "corpus case {i} ({kind}) disagrees with the python arm"
        );
        *counts.entry(kind.to_string()).or_default() += 1;
    }
    assert!(counts["holds"] >= 60, "holds corpus size: {counts:?}");
    let mutants: usize = counts
        .iter()
        .filter(|(k, _)| k.starts_with("mutant_"))
        .map(|(_, n)| n)
        .sum();
    assert!(mutants >= 60, "mutant corpus size: {counts:?}");
    assert!(
        counts["none_wrong_count"] >= 15,
        "none-branch corpus size: {counts:?}"
    );
}
