//! The mask family exercised end to end through provider dispatch:
//! the six membership-sweep relations over Simplex/ExtensionSet rows —
//! spec battery, named data mutants (every mutant flips a verdict),
//! refusals, and the frozen cross-implementation corpus replay.
//!
//! The test-side row emitter shares no code with the evaluators: it
//! writes `Op::Funa` field rows and `Op::Rela` membership rows
//! directly from the synthetic declaration index.

mod common;

use common::{provider, stack, STACK};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use serde_json::Value as J;

const OWN: [u8; 32] = [0xE5; 32];

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

/// Membership bodies in miniature: a complex with `n` vertices,
/// simplexes and extension sets as field rows + relation rows.
struct MaskBody {
    ops: Vec<Op>,
    next: u32,
    deps: Vec<[u8; 32]>,
}

impl MaskBody {
    fn new() -> MaskBody {
        MaskBody {
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

    /// A complex with `n` vertices.
    fn complex(&mut self, n: u64) -> u32 {
        let c = self.fresh();
        self.field("SimpC/n_vertices", c, natv(n));
        c
    }

    /// A simplex of `complex` with the given vertex mask.
    fn simplex(&mut self, complex: u32, verts: &[u64]) -> u32 {
        let s = self.fresh();
        self.field("Simplex/complex", s, lref(complex));
        for &v in verts {
            self.member("Simplex/contains", s, v);
        }
        s
    }

    /// An extension set over `simplex` with the given vertex mask.
    fn ext(&mut self, simplex: u32, verts: &[u64]) -> u32 {
        let e = self.fresh();
        self.field("ExtensionSet/simplex", e, lref(simplex));
        for &v in verts {
            self.member("ExtensionSet/contains", e, v);
        }
        e
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

fn ev_elems(name: &str, elems: &[u32], b: &MaskBody) -> Result<bool, String> {
    common::ev_elems(name, elems, &b.rows())
}

fn ev_elems_nat(name: &str, elems: &[u32], nat: u64, b: &MaskBody) -> Result<bool, String> {
    let mut vals: Vec<Value> = elems.iter().map(|e| lref(*e)).collect();
    vals.push(natv(nat));
    let refs: Vec<&Value> = vals.iter().collect();
    common::ev(name, &refs, &b.rows())
}

// ---------------------------------------------------------------------
// simplexSameMembers
// ---------------------------------------------------------------------

#[test]
fn same_members_holds_on_equal_masks() {
    let mut b = MaskBody::new();
    let k = b.complex(5);
    let s1 = b.simplex(k, &[0, 2, 4]);
    let s2 = b.simplex(k, &[4, 0, 2]); // order and duplicates immaterial
    b.member("Simplex/contains", s2, 0); // duplicate row, set semantics
    assert_eq!(ev_elems("simplexSameMembers", &[s1, s2], &b), Ok(true));
}

#[test]
fn same_members_mutant_extra_vertex_fails() {
    let mut b = MaskBody::new();
    let k = b.complex(5);
    let s1 = b.simplex(k, &[0, 2, 4]);
    let s2 = b.simplex(k, &[0, 2, 4, 1]); // the mutant: one extra member
    assert_eq!(ev_elems("simplexSameMembers", &[s1, s2], &b), Ok(false));
}

#[test]
fn same_members_mutant_missing_vertex_fails() {
    let mut b = MaskBody::new();
    let k = b.complex(5);
    let s1 = b.simplex(k, &[0, 2, 4]);
    let s2 = b.simplex(k, &[0, 2]); // the mutant: one member dropped
    assert_eq!(ev_elems("simplexSameMembers", &[s1, s2], &b), Ok(false));
}

// ---------------------------------------------------------------------
// simplexIsFaceMinus
// ---------------------------------------------------------------------

#[test]
fn face_minus_holds() {
    let mut b = MaskBody::new();
    let k = b.complex(4);
    let s = b.simplex(k, &[0, 1, 2]);
    let sface = b.simplex(k, &[0, 2]);
    // Field order: s, sface, v0.
    assert_eq!(
        ev_elems_nat("simplexIsFaceMinus", &[s, sface], 1, &b),
        Ok(true)
    );
}

#[test]
fn face_minus_removing_a_non_member_is_identity() {
    // v0 outside s's mask: s.mask minus {v0} == s.mask (set semantics,
    // mirroring the model's pointwise `s v && v ≠ v0`).
    let mut b = MaskBody::new();
    let k = b.complex(4);
    let s = b.simplex(k, &[0, 2]);
    let sface = b.simplex(k, &[0, 2]);
    assert_eq!(
        ev_elems_nat("simplexIsFaceMinus", &[s, sface], 1, &b),
        Ok(true)
    );
}

#[test]
fn face_minus_mutant_wrong_vertex_removed_fails() {
    let mut b = MaskBody::new();
    let k = b.complex(4);
    let s = b.simplex(k, &[0, 1, 2]);
    let sface = b.simplex(k, &[1, 2]); // removed 0, claimed v0 = 1
    assert_eq!(
        ev_elems_nat("simplexIsFaceMinus", &[s, sface], 1, &b),
        Ok(false)
    );
}

#[test]
fn face_minus_mutant_face_keeps_v0_fails() {
    let mut b = MaskBody::new();
    let k = b.complex(4);
    let s = b.simplex(k, &[0, 1, 2]);
    let sface = b.simplex(k, &[0, 1, 2]); // nothing removed
    assert_eq!(
        ev_elems_nat("simplexIsFaceMinus", &[s, sface], 1, &b),
        Ok(false)
    );
}

// ---------------------------------------------------------------------
// simplexIsIntersection
// ---------------------------------------------------------------------

#[test]
fn intersection_holds() {
    let mut b = MaskBody::new();
    let k = b.complex(6);
    let s1 = b.simplex(k, &[0, 1, 3]);
    let s2 = b.simplex(k, &[1, 3, 5]);
    let sint = b.simplex(k, &[1, 3]);
    // Field order: s1, s2, sint.
    assert_eq!(
        ev_elems("simplexIsIntersection", &[s1, s2, sint], &b),
        Ok(true)
    );
}

#[test]
fn intersection_mutant_extra_member_fails() {
    let mut b = MaskBody::new();
    let k = b.complex(6);
    let s1 = b.simplex(k, &[0, 1, 3]);
    let s2 = b.simplex(k, &[1, 3, 5]);
    let sint = b.simplex(k, &[1, 3, 5]); // 5 is not in s1
    assert_eq!(
        ev_elems("simplexIsIntersection", &[s1, s2, sint], &b),
        Ok(false)
    );
}

#[test]
fn intersection_mutant_missing_member_fails() {
    let mut b = MaskBody::new();
    let k = b.complex(6);
    let s1 = b.simplex(k, &[0, 1, 3]);
    let s2 = b.simplex(k, &[1, 3, 5]);
    let sint = b.simplex(k, &[1]); // dropped 3
    assert_eq!(
        ev_elems("simplexIsIntersection", &[s1, s2, sint], &b),
        Ok(false)
    );
}

// ---------------------------------------------------------------------
// extensionSetOmits
// ---------------------------------------------------------------------

#[test]
fn omits_holds_on_non_member() {
    let mut b = MaskBody::new();
    let k = b.complex(4);
    let sx = b.simplex(k, &[0, 1, 2]);
    let s = b.ext(sx, &[1]);
    assert_eq!(ev_elems_nat("extensionSetOmits", &[s], 2, &b), Ok(true));
}

#[test]
fn omits_mutant_member_row_flips_to_fails() {
    // The same body plus the one membership row for v: the negative
    // witness must flip.
    let mut b = MaskBody::new();
    let k = b.complex(4);
    let sx = b.simplex(k, &[0, 1, 2]);
    let s = b.ext(sx, &[1]);
    b.member("ExtensionSet/contains", s, 2);
    assert_eq!(ev_elems_nat("extensionSetOmits", &[s], 2, &b), Ok(false));
}

#[test]
fn omits_holds_past_the_vertex_bound() {
    // v at/past nVertices is in no mask (`containsNat` is false
    // there): omission holds — the ARGUMENT may sit out of range; only
    // membership ROWS out of range are unrepresentable.
    let mut b = MaskBody::new();
    let k = b.complex(4);
    let sx = b.simplex(k, &[0, 1]);
    let s = b.ext(sx, &[0]);
    assert_eq!(ev_elems_nat("extensionSetOmits", &[s], 9, &b), Ok(true));
}

// ---------------------------------------------------------------------
// extensionSetSameMembers
// ---------------------------------------------------------------------

#[test]
fn ext_same_members_holds() {
    let mut b = MaskBody::new();
    let k = b.complex(5);
    let sx1 = b.simplex(k, &[0, 1, 2, 3]);
    let sx2 = b.simplex(k, &[0, 1, 2]);
    // Distinct simplexes of ONE complex: masks share a universe and
    // compare (the guard is on the complex, not the simplex).
    let e1 = b.ext(sx1, &[1, 2]);
    let e2 = b.ext(sx2, &[2, 1]);
    assert_eq!(ev_elems("extensionSetSameMembers", &[e1, e2], &b), Ok(true));
}

#[test]
fn ext_same_members_mutant_flipped_row_fails() {
    let mut b = MaskBody::new();
    let k = b.complex(5);
    let sx = b.simplex(k, &[0, 1, 2, 3]);
    let e1 = b.ext(sx, &[1, 2]);
    let e2 = b.ext(sx, &[1, 3]); // the mutant: 2 → 3
    assert_eq!(
        ev_elems("extensionSetSameMembers", &[e1, e2], &b),
        Ok(false)
    );
}

// ---------------------------------------------------------------------
// isExtensionSetEmpty — the polarity pair, tested hard (the registry
// row adjudicates the design source's "nonemptiness" comment as a
// typo: the relation HOLDS iff S is EMPTY).
// ---------------------------------------------------------------------

#[test]
fn empty_extension_set_holds() {
    let mut b = MaskBody::new();
    let k = b.complex(3);
    let sx = b.simplex(k, &[0, 1, 2]);
    let s = b.ext(sx, &[]);
    assert_eq!(ev_elems("isExtensionSetEmpty", &[s], &b), Ok(true));
}

#[test]
fn nonempty_extension_set_fails() {
    let mut b = MaskBody::new();
    let k = b.complex(3);
    let sx = b.simplex(k, &[0, 1, 2]);
    let s = b.ext(sx, &[1]);
    assert_eq!(ev_elems("isExtensionSetEmpty", &[s], &b), Ok(false));
}

#[test]
fn empty_polarity_mutant_single_row_flips() {
    // One membership row is exactly the distance between the two
    // verdicts — a polarity-inverted evaluator would pass one of the
    // pair above and fail this flip.
    let mut b = MaskBody::new();
    let k = b.complex(3);
    let sx = b.simplex(k, &[0, 1, 2]);
    let s = b.ext(sx, &[]);
    assert_eq!(ev_elems("isExtensionSetEmpty", &[s], &b), Ok(true));
    b.member("ExtensionSet/contains", s, 0);
    assert_eq!(ev_elems("isExtensionSetEmpty", &[s], &b), Ok(false));
}

// ---------------------------------------------------------------------
// Refusals (undecidable is never a verdict)
// ---------------------------------------------------------------------

#[test]
fn unconstructed_simplex_refuses() {
    let mut b = MaskBody::new();
    let k = b.complex(4);
    let s1 = b.simplex(k, &[0]);
    let ghost = b.fresh(); // no rows at all
    let err = ev_elems("simplexSameMembers", &[s1, ghost], &b).unwrap_err();
    assert!(
        err.contains("no `Simplex/complex` row"),
        "unconstructed element must refuse: {err}"
    );
}

#[test]
fn out_of_range_membership_row_refuses() {
    // A membership row at/past nVertices corresponds to no model
    // state (the masks are Fin-indexed): refusal, never "ignored".
    let mut b = MaskBody::new();
    let k = b.complex(3);
    let s1 = b.simplex(k, &[0, 7]); // 7 ≥ 3
    let s2 = b.simplex(k, &[0]);
    let err = ev_elems("simplexSameMembers", &[s1, s2], &b).unwrap_err();
    assert!(
        err.contains("at or past the complex's"),
        "out-of-range membership must refuse: {err}"
    );
}

#[test]
fn cross_complex_comparison_refuses() {
    let mut b = MaskBody::new();
    let k1 = b.complex(4);
    let k2 = b.complex(4);
    let s1 = b.simplex(k1, &[0]);
    let s2 = b.simplex(k2, &[0]);
    let err = ev_elems("simplexSameMembers", &[s1, s2], &b).unwrap_err();
    assert!(
        err.contains("row-grain distinct complex"),
        "cross-complex comparison must refuse: {err}"
    );
}

#[test]
fn ambiguous_complex_refuses() {
    let mut b = MaskBody::new();
    let k1 = b.complex(4);
    let k2 = b.complex(4);
    let s1 = b.simplex(k1, &[0]);
    b.field("Simplex/complex", s1, lref(k2)); // conflicting field row
    let s2 = b.simplex(k1, &[0]);
    let err = ev_elems("simplexSameMembers", &[s1, s2], &b).unwrap_err();
    assert!(
        err.contains("ambiguous `Simplex/complex`"),
        "conflicting field rows must refuse: {err}"
    );
}

#[test]
fn missing_n_vertices_refuses() {
    let mut b = MaskBody::new();
    let bare = b.fresh(); // a complex element with no n_vertices row
    let s1 = b.simplex(bare, &[0]);
    let s2 = b.simplex(bare, &[0]);
    let err = ev_elems("simplexSameMembers", &[s1, s2], &b).unwrap_err();
    assert!(
        err.contains("no `SimpC/n_vertices` row"),
        "missing vertex count must refuse: {err}"
    );
}

#[test]
fn non_nat_vertex_in_membership_row_refuses() {
    let mut b = MaskBody::new();
    let k = b.complex(4);
    let sx = b.simplex(k, &[0]);
    let s = b.ext(sx, &[]);
    // A membership row whose vertex cell is a Q literal.
    b.ops.push(Op::Rela {
        rel: b.xref(s_fun("ExtensionSet/contains")),
        args: vec![lref(s), Value::Lit(Literal::q(1, 2).expect("canonical q"))],
    });
    let err = ev_elems("isExtensionSetEmpty", &[s], &b).unwrap_err();
    assert!(
        err.contains("vertex is not a Nat literal"),
        "non-Nat vertex must refuse: {err}"
    );
}

#[test]
fn wrong_arity_membership_row_refuses() {
    let mut b = MaskBody::new();
    let k = b.complex(4);
    let sx = b.simplex(k, &[0]);
    b.ops.push(Op::Rela {
        rel: b.xref(s_fun("Simplex/contains")),
        args: vec![lref(sx), natv(1), natv(2)],
    });
    let s2 = b.simplex(k, &[0, 1]);
    let err = ev_elems("simplexSameMembers", &[sx, s2], &b).unwrap_err();
    assert!(
        err.contains("expected 2 arguments"),
        "wrong-arity membership row must refuse: {err}"
    );
}

#[test]
fn external_complex_ref_refuses() {
    let mut b = MaskBody::new();
    let s1 = b.fresh();
    // Simplex/complex pointing at an element of another body: the row
    // context is single-body, so the chain cannot resolve.
    let foreign = Value::Ref(ElemRef::External {
        dep_index: 0,
        counter: 999,
    });
    b.field("Simplex/complex", s1, foreign);
    let k = b.complex(3);
    let s2 = b.simplex(k, &[0]);
    let err = ev_elems("simplexSameMembers", &[s1, s2], &b).unwrap_err();
    assert!(
        err.contains("external element ref"),
        "external complex must refuse: {err}"
    );
}

#[test]
fn literal_argument_where_element_expected_refuses() {
    let mut b = MaskBody::new();
    let k = b.complex(3);
    let sx = b.simplex(k, &[0]);
    let _ = sx;
    let vals = [natv(3)];
    let refs: Vec<&Value> = vals.iter().collect();
    let err = common::ev("isExtensionSetEmpty", &refs, &b.rows()).unwrap_err();
    assert!(
        err.contains("element ref"),
        "literal where an element belongs must refuse: {err}"
    );
}

#[test]
fn provider_claims_all_six() {
    let p = provider();
    for name in [
        "extensionSetOmits",
        "extensionSetSameMembers",
        "isExtensionSetEmpty",
        "simplexIsFaceMinus",
        "simplexIsIntersection",
        "simplexSameMembers",
    ] {
        assert!(p.local_by_name(name).is_some(), "`{name}` claimed");
    }
}

// ---------------------------------------------------------------------
// The frozen cross-implementation corpus (python set-algebra arm):
// replay every instance through provider dispatch and require verdict
// agreement. Disagreement = stop-and-investigate, never
// adjust-the-corpus.
// ---------------------------------------------------------------------

fn corpus() -> J {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/masks_pyref_corpus.json"
    );
    serde_json::from_str(&std::fs::read_to_string(path).expect("corpus present"))
        .expect("corpus parses")
}

fn verts(j: &J) -> Vec<u64> {
    j.as_array()
        .expect("vertex list")
        .iter()
        .map(|v| v.as_u64().expect("vertex"))
        .collect()
}

#[test]
fn pyref_same_members() {
    let c = corpus();
    let mut n = 0;
    for case in c["same_members"].as_array().expect("list") {
        let mut b = MaskBody::new();
        let k = b.complex(case["n"].as_u64().expect("n"));
        let s1 = b.simplex(k, &verts(&case["s1"]));
        let s2 = b.simplex(k, &verts(&case["s2"]));
        assert_eq!(
            ev_elems("simplexSameMembers", &[s1, s2], &b),
            Ok(case["verdict"].as_bool().expect("verdict")),
            "same_members case {n} disagrees with the python arm"
        );
        n += 1;
    }
    assert!(n >= 60, "corpus size");
}

#[test]
fn pyref_face_minus() {
    let c = corpus();
    let mut n = 0;
    for case in c["face_minus"].as_array().expect("list") {
        let mut b = MaskBody::new();
        let k = b.complex(case["n"].as_u64().expect("n"));
        let s = b.simplex(k, &verts(&case["s"]));
        let sface = b.simplex(k, &verts(&case["sface"]));
        let v0 = case["v0"].as_u64().expect("v0");
        assert_eq!(
            ev_elems_nat("simplexIsFaceMinus", &[s, sface], v0, &b),
            Ok(case["verdict"].as_bool().expect("verdict")),
            "face_minus case {n} disagrees with the python arm"
        );
        n += 1;
    }
    assert!(n >= 60, "corpus size");
}

#[test]
fn pyref_intersection() {
    let c = corpus();
    let mut n = 0;
    for case in c["intersection"].as_array().expect("list") {
        let mut b = MaskBody::new();
        let k = b.complex(case["n"].as_u64().expect("n"));
        let s1 = b.simplex(k, &verts(&case["s1"]));
        let s2 = b.simplex(k, &verts(&case["s2"]));
        let sint = b.simplex(k, &verts(&case["sint"]));
        assert_eq!(
            ev_elems("simplexIsIntersection", &[s1, s2, sint], &b),
            Ok(case["verdict"].as_bool().expect("verdict")),
            "intersection case {n} disagrees with the python arm"
        );
        n += 1;
    }
    assert!(n >= 60, "corpus size");
}
