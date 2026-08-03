//! The applicability families exercised end to end through provider
//! dispatch, against a test-side emitter that shares no code with the
//! evaluators, with a mutant battery per family (each mutant must flip
//! the verdict).
//!
//! This file is the row-grain spec battery: hand-constructed instances
//! whose expected verdicts come straight from the Lean catalogue's
//! definitions.

mod common;

use common::{ev, ev_elems, stack, STACK};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use std::collections::HashMap;

// ---------------------------------------------------------------------
// Little ASTs
// ---------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
enum T {
    Var(u32),
    Const(i64, u64),
    Add(Box<T>, Box<T>),
    Sub(Box<T>, Box<T>),
    Mul(Box<T>, Box<T>),
    Neg(Box<T>),
    Idx(Box<T>, u64),
}

#[derive(Debug, Clone, PartialEq)]
enum F {
    Atom(u8, T, T),
    And(Box<F>, Box<F>),
    True,
}

fn v(w: u32) -> T {
    T::Var(w)
}
fn c(n: i64) -> T {
    T::Const(n, 1)
}
fn add(l: T, r: T) -> T {
    T::Add(Box::new(l), Box::new(r))
}
fn sub(l: T, r: T) -> T {
    T::Sub(Box::new(l), Box::new(r))
}
fn mul(l: T, r: T) -> T {
    T::Mul(Box::new(l), Box::new(r))
}
fn neg(x: T) -> T {
    T::Neg(Box::new(x))
}
fn atom(b: u8, l: T, r: T) -> F {
    F::Atom(b, l, r)
}
fn fand(l: F, r: F) -> F {
    F::And(Box::new(l), Box::new(r))
}

/// The pinned farkasEntries encoding: right-nested Add of
/// Mul(Const λ, e), Const 0 end.
fn entries_term(entries: &[(i64, u64, T)]) -> T {
    let mut out = c(0);
    for (n, d, e) in entries.iter().rev() {
        out = add(mul(T::Const(*n, *d), e.clone()), out);
    }
    out
}

// ---------------------------------------------------------------------
// The test-side row emitter
// ---------------------------------------------------------------------

const OWN: [u8; 32] = [0xE3; 32];

struct Body {
    ops: Vec<Op>,
    deps: Vec<[u8; 32]>,
    fun: HashMap<&'static str, Chid>,
    sort: HashMap<&'static str, Chid>,
    wires: HashMap<u32, u32>,
}

impl Body {
    fn new() -> Body {
        let s = stack();
        let mut fun = HashMap::new();
        for name in [
            "TVar",
            "TConst",
            "TAdd",
            "TSub",
            "TMul",
            "TNeg",
            "TIdx",
            "FAtomLT",
            "FAtomLE",
            "FAtomEQ",
            "FAtomGE",
            "FAtomGT",
            "FAtomNE",
            "FAnd",
            "FTrue",
            "Judgment/pre",
            "Judgment/post",
            "Proof/concludes",
            "PSyzygy/nComponents",
            "PSyzygy/component",
            "PSyzygy/combinationCoeffs",
            "PSyzygy/conclusion",
            "PSyzygy/proof",
            "PPsdCertT/n",
            "PPsdCertT/A",
            "PPsdCertT/Z",
            "PPsdCertT/term",
            "PPsdCertT/conclusion",
            "PPsdCertDD/n",
            "PPsdCertDD/A",
            "PPsdCertDD/Z",
            "PPsdCertK/m",
            "PPsdCertK/k",
            "PPsdCertK/nTotal",
            "PPsdCertK/A",
            "PPsdCertK/N",
            "PPsdCertK/B",
            "PPsdCertK/innerT",
            "PPsdCertK/Z",
            "Wire/type",
            "mkTensorType",
            "cons",
            "empty",
        ] {
            fun.insert(name, s.fun(name).expect(name).chid);
        }
        let mut sort = HashMap::new();
        for name in [
            "Term",
            "Formula",
            "Wire",
            "Judgment",
            "Proof",
            "PSyzygy",
            "PPsdCertT",
            "PPsdCertDD",
            "PPsdCertK",
            "TensorType",
            "Shape",
            "Dtype",
        ] {
            sort.insert(name, s.sort(name).expect(name));
        }
        Body {
            ops: Vec::new(),
            deps: vec![STACK],
            fun,
            sort,
            wires: HashMap::new(),
        }
    }

    fn ext(&self, chid: Chid) -> ElemRef {
        let dep_index = self
            .deps
            .iter()
            .position(|h| *h == chid.0)
            .expect("chid homed in deps") as u32;
        ElemRef::External {
            dep_index,
            counter: chid.1,
        }
    }

    fn elta(&mut self, sort: &'static str) -> u32 {
        let e = self.ops.len() as u32;
        self.ops.push(Op::Elta {
            sort: self.ext(self.sort[sort]),
        });
        e
    }

    fn lref(e: u32) -> Value {
        Value::Ref(ElemRef::Local(e))
    }

    fn nat(n: u64) -> Value {
        Value::Lit(Literal::nat(n))
    }

    /// Element + its constructor row.
    fn ctor(&mut self, sort: &'static str, fun: &'static str, args: Vec<Value>) -> u32 {
        let e = self.elta(sort);
        self.ops.push(Op::Funa {
            fun: self.ext(self.fun[fun]),
            args,
            value: Self::lref(e),
        });
        e
    }

    /// A field row `fun(args) = value` (no new element).
    fn field(&mut self, fun: &'static str, args: Vec<Value>, value: Value) {
        self.ops.push(Op::Funa {
            fun: self.ext(self.fun[fun]),
            args,
            value,
        });
    }

    fn wire(&mut self, id: u32) -> u32 {
        if let Some(e) = self.wires.get(&id) {
            return *e;
        }
        let e = self.elta("Wire");
        self.wires.insert(id, e);
        e
    }

    /// Type a wire at the given shape (B14 family): Wire/type →
    /// mkTensorType{dtype, shape} with a cons-list shape. The dtype
    /// slot is a bare element (the walk never resolves it).
    fn type_wire(&mut self, wire_id: u32, shape: &[u64]) {
        let we = self.wire(wire_id);
        let dt = self.elta("Dtype");
        let mut sh = self.ctor("Shape", "empty", vec![]);
        for extent in shape.iter().rev() {
            sh = self.ctor("Shape", "cons", vec![Self::nat(*extent), Self::lref(sh)]);
        }
        let tt = self.ctor(
            "TensorType",
            "mkTensorType",
            vec![Self::lref(dt), Self::lref(sh)],
        );
        self.field("Wire/type", vec![Self::lref(we)], Self::lref(tt));
    }

    fn term(&mut self, t: &T) -> u32 {
        match t {
            T::Var(w) => {
                let we = self.wire(*w);
                self.ctor("Term", "TVar", vec![Self::lref(we)])
            }
            T::Const(n, d) => {
                let lit = Literal::q(*n, *d).expect("canonical q");
                self.ctor("Term", "TConst", vec![Value::Lit(lit)])
            }
            T::Neg(x) => {
                let xe = self.term(x);
                self.ctor("Term", "TNeg", vec![Self::lref(xe)])
            }
            T::Idx(x, i) => {
                let xe = self.term(x);
                // field order bytewise: i, t.
                self.ctor("Term", "TIdx", vec![Self::nat(*i), Self::lref(xe)])
            }
            T::Add(l, r) | T::Sub(l, r) | T::Mul(l, r) => {
                let name = match t {
                    T::Add(..) => "TAdd",
                    T::Sub(..) => "TSub",
                    _ => "TMul",
                };
                let le = self.term(l);
                let re = self.term(r);
                self.ctor("Term", name, vec![Self::lref(le), Self::lref(re)])
            }
        }
    }

    fn formula(&mut self, f: &F) -> u32 {
        match f {
            F::Atom(b, l, r) => {
                let name = [
                    "FAtomLT", "FAtomLE", "FAtomEQ", "FAtomGE", "FAtomGT", "FAtomNE",
                ][usize::from((*b).min(5))];
                let le = self.term(l);
                let re = self.term(r);
                self.ctor("Formula", name, vec![Self::lref(le), Self::lref(re)])
            }
            F::And(l, r) => {
                let le = self.formula(l);
                let re = self.formula(r);
                self.ctor("Formula", "FAnd", vec![Self::lref(le), Self::lref(re)])
            }
            F::True => self.ctor("Formula", "FTrue", vec![]),
        }
    }

    /// A proof element concluding (pre, post).
    fn proof(&mut self, pre: &F, post: &F) -> u32 {
        let pe = self.formula(pre);
        let po = self.formula(post);
        let j = self.elta("Judgment");
        self.field("Judgment/pre", vec![Self::lref(j)], Self::lref(pe));
        self.field("Judgment/post", vec![Self::lref(j)], Self::lref(po));
        let p = self.elta("Proof");
        self.field("Proof/concludes", vec![Self::lref(p)], Self::lref(j));
        p
    }

    /// A PSyzygy node: components conclude (pre_k, post_k); the node's
    /// own proof concludes (pre, post).
    #[allow(clippy::too_many_arguments)]
    fn syzygy(&mut self, pre: &F, post: &F, components: &[(F, F)], cc: &T, conclusion: &T) -> u32 {
        let node = self.elta("PSyzygy");
        let proof = self.proof(pre, post);
        self.field("PSyzygy/proof", vec![Self::lref(node)], Self::lref(proof));
        self.field(
            "PSyzygy/nComponents",
            vec![Self::lref(node)],
            Self::nat(components.len() as u64),
        );
        for (k, (cpre, cpost)) in components.iter().enumerate() {
            let cp = self.proof(cpre, cpost);
            // field order bytewise: k, p.
            self.field(
                "PSyzygy/component",
                vec![Self::nat(k as u64), Self::lref(node)],
                Self::lref(cp),
            );
        }
        let cce = self.term(cc);
        let cone = self.term(conclusion);
        self.field(
            "PSyzygy/combinationCoeffs",
            vec![Self::lref(node)],
            Self::lref(cce),
        );
        self.field(
            "PSyzygy/conclusion",
            vec![Self::lref(node)],
            Self::lref(cone),
        );
        node
    }

    fn q_tensor(extents: &[u64], vals: &[(i64, u64)]) -> Value {
        Value::Lit(Literal::tensor_inline_q(extents, vals).expect("inline tensor"))
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

// ---------------------------------------------------------------------
// polynomialCanonicalEq
// ---------------------------------------------------------------------

#[test]
fn poly_canonical_eq_battery() {
    let mut b = Body::new();
    // (x + 1)^2 == x^2 + 2x + 1 — value-exact, different ASTs.
    let x = || v(0);
    let sq = mul(add(x(), c(1)), add(x(), c(1)));
    let expanded = add(add(mul(x(), x()), mul(c(2), x())), c(1));
    let wrong = add(add(mul(x(), x()), mul(c(2), x())), c(2));
    let l = b.term(&sq);
    let r = b.term(&expanded);
    let w = b.term(&wrong);
    // 2x + 2 vs x + 1: value-DIFFERENT (F7: no rescale — these are
    // different polynomials, not "the same up to scale").
    let two_x_two = add(mul(c(2), x()), c(2));
    let x_one = add(x(), c(1));
    let s1 = b.term(&two_x_two);
    let s2 = b.term(&x_one);
    // idx-ful side → decidedly false (the PNorm idx-free gate).
    let idxful = T::Idx(Box::new(v(1)), 0);
    let ix = b.term(&idxful);
    let rows = b.rows();
    assert_eq!(ev_elems("polynomialCanonicalEq", &[l, r], &rows), Ok(true));
    assert_eq!(ev_elems("polynomialCanonicalEq", &[l, w], &rows), Ok(false));
    assert_eq!(
        ev_elems("polynomialCanonicalEq", &[s1, s2], &rows),
        Ok(false),
        "primitive-rescale equality would be anRta here — F7"
    );
    assert_eq!(
        ev_elems("polynomialCanonicalEq", &[ix, ix], &rows),
        Ok(false),
        "idx-free gate: even syntactically identical idx terms refuse the relation"
    );
}

#[test]
fn poly_canonical_eq_refusals() {
    let mut b = Body::new();
    let l = b.term(&c(1));
    // An element with NO constructor row in view.
    let bare = b.elta("Term");
    // An element with TWO constructor rows (P-FUN territory).
    let amb = b.elta("Term");
    let one = Value::Lit(Literal::q(1, 1).expect("q"));
    b.ops.push(Op::Funa {
        fun: b.ext(b.fun["TConst"]),
        args: vec![one.clone()],
        value: Body::lref(amb),
    });
    b.ops.push(Op::Funa {
        fun: b.ext(b.fun["TConst"]),
        args: vec![one],
        value: Body::lref(amb),
    });
    let rows = b.rows();
    let bare_err = ev_elems("polynomialCanonicalEq", &[l, bare], &rows).unwrap_err();
    assert!(
        bare_err.contains("row-context argument"),
        "unconstructed element refuses with a row-context reason: {bare_err}"
    );
    let amb_err = ev_elems("polynomialCanonicalEq", &[l, amb], &rows).unwrap_err();
    assert!(
        amb_err.contains("row-context argument"),
        "ambiguous element refuses with a row-context reason: {amb_err}"
    );
}

// ---------------------------------------------------------------------
// premiseContains / syzygyConclusionFormRel
// ---------------------------------------------------------------------

#[test]
fn premise_contains_battery() {
    let mut b = Body::new();
    let a1 = || atom(1, v(0), c(0));
    let a2 = || atom(2, v(1), c(3));
    let a3 = || atom(3, v(2), c(1));
    let pre = fand(fand(a1(), a2()), a3());
    let sub_good = fand(a3(), a1()); // reordered — containment is set-wise
    let sub_bad = fand(a1(), atom(1, v(0), c(7)));
    let pre_e = b.formula(&pre);
    // Emit subs WITHOUT interning (fresh elements) — the containment
    // must hold by STRUCTURE, not element identity.
    let sub_g = b.formula(&sub_good);
    let sub_b = b.formula(&sub_bad);
    let rows = b.rows();
    assert_eq!(
        ev_elems("premiseContains", &[pre_e, sub_g], &rows),
        Ok(true)
    );
    assert_eq!(
        ev_elems("premiseContains", &[pre_e, sub_b], &rows),
        Ok(false)
    );
    // The whole pre is a sub-conjunction of itself.
    assert_eq!(
        ev_elems("premiseContains", &[pre_e, pre_e], &rows),
        Ok(true)
    );
}

#[test]
fn syzygy_conclusion_form_readings() {
    let mut b = Body::new();
    let concl = add(v(0), c(-2));
    // Reading 1: (conclusion <= 0).
    let f_zero = atom(1, concl.clone(), c(0));
    // Reading 2: conclusion = neg e, formula = (e >= 0).
    let e_inner = add(v(1), c(5));
    let concl_neg = neg(e_inner.clone());
    let f_ge = atom(3, e_inner.clone(), c(0));
    // Reading 3: conclusion = l - r, formula = (l <= r).
    let concl_sub = sub(v(2), c(4));
    let f_lit = atom(1, v(2), c(4));
    // Negatives: wrong polarity / wrong shape.
    let f_wrong = atom(3, concl.clone(), c(0));
    let ce = b.term(&concl);
    let fz = b.formula(&f_zero);
    let cn = b.term(&concl_neg);
    let fg = b.formula(&f_ge);
    let cs = b.term(&concl_sub);
    let fl = b.formula(&f_lit);
    let fw = b.formula(&f_wrong);
    let rows = b.rows();
    assert_eq!(
        ev_elems("syzygyConclusionFormRel", &[ce, fz], &rows),
        Ok(true)
    );
    assert_eq!(
        ev_elems("syzygyConclusionFormRel", &[cn, fg], &rows),
        Ok(true)
    );
    assert_eq!(
        ev_elems("syzygyConclusionFormRel", &[cs, fl], &rows),
        Ok(true)
    );
    assert_eq!(
        ev_elems("syzygyConclusionFormRel", &[ce, fw], &rows),
        Ok(false)
    );
    assert_eq!(
        ev_elems("syzygyConclusionFormRel", &[cn, fz], &rows),
        Ok(false)
    );
}

// ---------------------------------------------------------------------
// farkasCombinationValid
// ---------------------------------------------------------------------

/// Sound instance: premise (x - 3 <= 0) AND (0 <= y i.e. y >= 0 as a
/// ge-atom => normal form -y) AND (u = 2); conclusion
/// 2*(x - 3) + 1*(-y) + 3*(u - 2) with lambdas (2, 1, 3).
fn farkas_fixture() -> (F, T, T) {
    let a_le = atom(1, sub(v(0), c(3)), c(0)); // x - 3 <= 0 → x - 3
    let a_ge = atom(3, v(1), c(0)); // y >= 0 → -y
    let a_eq = atom(2, v(2), c(2)); // u = 2 → u - 2 and 2 - u
    let premise = fand(fand(a_le, a_ge), a_eq);
    let cc = entries_term(&[
        (2, 1, sub(v(0), c(3))),
        (1, 1, sub(c(0), v(1))),
        (3, 1, sub(v(2), c(2))),
    ]);
    // conclusion = 2x - 6 - y + 3u - 6 = 2x - y + 3u - 12 (any AST
    // with that canonical form; the value-exact arm).
    let conclusion = add(
        add(mul(c(2), v(0)), neg(v(1))),
        add(mul(c(3), v(2)), c(-12)),
    );
    (premise, cc, conclusion)
}

#[test]
fn farkas_combination_battery() {
    let (premise, cc, conclusion) = farkas_fixture();
    let mut b = Body::new();
    let pe = b.formula(&premise);
    let cce = b.term(&cc);
    let ce = b.term(&conclusion);
    // Mutants:
    // 1. negative lambda on a non-eq entry.
    let cc_neg = entries_term(&[(-2, 1, sub(v(0), c(3)))]);
    let concl_neg = mul(c(-2), sub(v(0), c(3)));
    let cce_n = b.term(&cc_neg);
    let ce_n = b.term(&concl_neg);
    // 2. wrong conclusion (off by one).
    let concl_wrong = add(
        add(mul(c(2), v(0)), neg(v(1))),
        add(mul(c(3), v(2)), c(-11)),
    );
    let ce_w = b.term(&concl_wrong);
    // 3. cc not the pinned encoding (missing zero terminator).
    let cc_bad = mul(c(2), sub(v(0), c(3)));
    let cce_b = b.term(&cc_bad);
    // 4. vehicle matching NO premise polynomial.
    let cc_nomatch = entries_term(&[(2, 1, sub(v(0), c(4)))]);
    let concl_nomatch = mul(c(2), sub(v(0), c(4)));
    let cce_m = b.term(&cc_nomatch);
    let ce_m = b.term(&concl_nomatch);
    let rows = b.rows();
    // field order: combinationCoeffs, conclusion, premise.
    assert_eq!(
        ev_elems("farkasCombinationValid", &[cce, ce, pe], &rows),
        Ok(true)
    );
    assert_eq!(
        ev_elems("farkasCombinationValid", &[cce_n, ce_n, pe], &rows),
        Ok(false),
        "negative lambda refuses even where the fold matches"
    );
    assert_eq!(
        ev_elems("farkasCombinationValid", &[cce, ce_w, pe], &rows),
        Ok(false)
    );
    assert_eq!(
        ev_elems("farkasCombinationValid", &[cce_b, ce, pe], &rows),
        Ok(false)
    );
    assert_eq!(
        ev_elems("farkasCombinationValid", &[cce_m, ce_m, pe], &rows),
        Ok(false)
    );
}

#[test]
fn farkas_eq_both_polarities() {
    // The eq atom exposes BOTH polarities: a nonneg weight on (2 - u)
    // is exactly how "negative weight on (u - 2)" is spelled.
    let a_eq = atom(2, v(2), c(2));
    let premise = fand(F::True, a_eq);
    let cc = entries_term(&[(5, 2, sub(c(2), v(2)))]);
    let conclusion = mul(T::Const(5, 2), sub(c(2), v(2)));
    let mut b = Body::new();
    let pe = b.formula(&premise);
    let cce = b.term(&cc);
    let ce = b.term(&conclusion);
    let rows = b.rows();
    assert_eq!(
        ev_elems("farkasCombinationValid", &[cce, ce, pe], &rows),
        Ok(true)
    );
}

#[test]
fn farkas_wire_coordinate_branch() {
    // The G1 W branch: every polynomial rides TIdx projections.
    let x0 = || T::Idx(Box::new(v(0)), 0);
    let x1 = || T::Idx(Box::new(v(0)), 1);
    let a1 = atom(1, sub(x0(), c(1)), c(0)); // x[0] - 1 <= 0
    let a2 = atom(1, x1(), c(0)); // x[1] <= 0
    let premise = fand(a1, a2);
    let cc = entries_term(&[(1, 1, sub(x0(), c(1))), (2, 1, x1())]);
    let conclusion = add(sub(x0(), c(1)), mul(c(2), x1()));
    let mut b = Body::new();
    let pe = b.formula(&premise);
    let cce = b.term(&cc);
    let ce = b.term(&conclusion);
    // MIXED probe: a bare-wire vehicle alongside idx atoms. The Lean
    // catalogue's two branches BOTH reject this shape (core: idx-ful
    // atoms gated out; W: bare wire untranslatable) — but the python
    // reference, a second independent checker, and the real producer corpus (
    // iface composites, found by the three-way differential) all
    // accept it, so the evaluator carries the consensus MIXED branch
    // (see blapplic.rs `mixed_poly`'s spec-divergence note; Lean-side
    // widening is the pending adjudication).
    let cc_mixed = entries_term(&[(1, 1, sub(x0(), c(1))), (1, 1, v(3))]);
    let a3 = atom(1, v(3), c(0));
    let premise_mixed = fand(fand(a1_clone(), a3), F::True);
    let concl_mixed = add(sub(x0(), c(1)), v(3));
    fn a1_clone() -> F {
        atom(
            1,
            sub(T::Idx(Box::new(T::Var(0)), 0), T::Const(1, 1)),
            T::Const(0, 1),
        )
    }
    let pm = b.formula(&premise_mixed);
    let ccm = b.term(&cc_mixed);
    let cm = b.term(&concl_mixed);
    let rows = b.rows();
    assert_eq!(
        ev_elems("farkasCombinationValid", &[cce, ce, pe], &rows),
        Ok(true),
        "all-idx combination rides the wire-coordinate branch"
    );
    assert_eq!(
        ev_elems("farkasCombinationValid", &[ccm, cm, pm], &rows),
        Ok(true),
        "mixed bare-wire + idx combination rides the consensus MIXED \
         branch (cross-implementation and corpus agreement; the Lean branches \
         alone would reject — the recorded divergence)"
    );
}

// ---------------------------------------------------------------------
// syzygyCombinationValid (the B11 node walk)
// ---------------------------------------------------------------------

#[test]
fn syzygy_node_battery() {
    // Components prove (x <= 0) and (y - 1 <= 0) from sub-conjunctions
    // of the composite premise; the premise also carries (u = 2) as an
    // equality conjunct. Combination: 1*x + 2*(y - 1) + 1*(2 - u).
    let ax = atom(1, v(0), c(0));
    let ay = atom(1, sub(v(1), c(1)), c(0));
    let aeq = atom(2, v(2), c(2));
    let premise = fand(fand(ax.clone(), ay.clone()), aeq.clone());
    let post = atom(1, v(9), c(0)); // the composite post (opaque here)
    let comp1 = (ax.clone(), atom(1, v(0), c(0))); // proves x <= 0
    let comp2 = (fand(ax, ay), atom(1, sub(v(1), c(1)), c(0)));
    let cc = entries_term(&[
        (1, 1, v(0)),
        (2, 1, sub(v(1), c(1))),
        (1, 1, sub(c(2), v(2))),
    ]);
    let conclusion = add(add(v(0), mul(c(2), sub(v(1), c(1)))), sub(c(2), v(2)));
    let mut b = Body::new();
    let node = b.syzygy(&premise, &post, &[comp1, comp2], &cc, &conclusion);
    let rows = b.rows();
    assert_eq!(ev_elems("syzygyCombinationValid", &[node], &rows), Ok(true));

    // premiseContains legs (the separate relation the axioms bind).
    let mut b2 = Body::new();
    let ax2 = atom(1, v(0), c(0));
    let ay2 = atom(1, sub(v(1), c(1)), c(0));
    let aeq2 = atom(2, v(2), c(2));
    let pre_e = b2.formula(&fand(fand(ax2.clone(), ay2.clone()), aeq2));
    let sub_e = b2.formula(&fand(ax2, ay2));
    let rows2 = b2.rows();
    assert_eq!(
        ev_elems("premiseContains", &[pre_e, sub_e], &rows2),
        Ok(true)
    );

    // Mutant: a vehicle sourced from NEITHER a component post nor an
    // equality premise conjunct — the non-eq premise atom (x <= 0) is
    // legal for FARKAS but not as a syzygy premise-side source when it
    // matches no component post... here (y - 1) DOES match comp2's
    // post, so mutate to an unmatched vehicle instead.
    let cc_bad = entries_term(&[(1, 1, sub(v(1), c(7)))]);
    let concl_bad = sub(v(1), c(7));
    let mut b3 = Body::new();
    let ax3 = atom(1, v(0), c(0));
    let premise3 = fand(ax3.clone(), F::True);
    let node3 = b3.syzygy(
        &premise3,
        &atom(1, v(9), c(0)),
        &[(ax3.clone(), ax3)],
        &cc_bad,
        &concl_bad,
    );
    let rows3 = b3.rows();
    assert_eq!(
        ev_elems("syzygyCombinationValid", &[node3], &rows3),
        Ok(false)
    );
}

#[test]
fn syzygy_premise_side_is_eq_only() {
    // A NON-equality premise conjunct is not a legal syzygy entry
    // source (components carry the inequalities; the premise side is
    // the eq-wiring channel only — Lean syzygyCheckCore).
    let ale = atom(1, v(0), c(0)); // x <= 0, non-eq
    let premise = fand(ale, F::True);
    let post = atom(1, v(9), c(0));
    let cc = entries_term(&[(1, 1, v(0))]);
    let conclusion = v(0);
    let mut b = Body::new();
    // ZERO components: the only candidate source is the premise atom,
    // which is not an eq atom → no match → false.
    let node = b.syzygy(&premise, &post, &[], &cc, &conclusion);
    let rows = b.rows();
    assert_eq!(
        ev_elems("syzygyCombinationValid", &[node], &rows),
        Ok(false)
    );
}

// ---------------------------------------------------------------------
// PsdCert
// ---------------------------------------------------------------------

/// A 2x2 T-witness instance: A = [[2,-1],[-1,2]] (PD), Z = [[1,1/2],[0,1]]
/// → A·Z = [[2,0],[-1,3/2]] lower-triangular, positive diagonal.
fn psd_t_node(b: &mut Body, forge: Option<&str>) -> u32 {
    let node = b.elta("PPsdCertT");
    b.field("PPsdCertT/n", vec![Body::lref(node)], Body::nat(2));
    let a = match forge {
        Some("asym") => Body::q_tensor(&[2, 2], &[(2, 1), (-1, 1), (1, 1), (2, 1)]),
        Some("negdiag") => Body::q_tensor(&[2, 2], &[(-2, 1), (1, 1), (1, 1), (-2, 1)]),
        Some("shape") => {
            Body::q_tensor(&[2, 3], &[(2, 1), (-1, 1), (0, 1), (-1, 1), (2, 1), (0, 1)])
        }
        _ => Body::q_tensor(&[2, 2], &[(2, 1), (-1, 1), (-1, 1), (2, 1)]),
    };
    let z = match forge {
        Some("lowz") => Body::q_tensor(&[2, 2], &[(1, 1), (1, 2), (1, 3), (1, 1)]),
        _ => Body::q_tensor(&[2, 2], &[(1, 1), (1, 2), (0, 1), (1, 1)]),
    };
    b.field("PPsdCertT/A", vec![Body::lref(node)], a);
    b.field("PPsdCertT/Z", vec![Body::lref(node)], z);
    node
}

#[test]
fn psd_cert_t_witness_battery() {
    let mut b = Body::new();
    let good = psd_t_node(&mut b, None);
    let asym = psd_t_node(&mut b, Some("asym"));
    let negd = psd_t_node(&mut b, Some("negdiag"));
    let shp = psd_t_node(&mut b, Some("shape"));
    let lowz = psd_t_node(&mut b, Some("lowz"));
    let rows = b.rows();
    assert_eq!(ev_elems("psdCertTWitness", &[good], &rows), Ok(true));
    assert_eq!(ev_elems("psdCertTWitness", &[asym], &rows), Ok(false));
    assert_eq!(ev_elems("psdCertTWitness", &[negd], &rows), Ok(false));
    assert_eq!(
        ev_elems("psdCertTWitness", &[shp], &rows),
        Ok(false),
        "shape disagreement is the witness relation's first clause — decided false"
    );
    assert_eq!(ev_elems("psdCertTWitness", &[lowz], &rows), Ok(false));
}

#[test]
fn psd_cert_t_concl_battery() {
    let mut b = Body::new();
    let node = psd_t_node(&mut b, None);
    // terms (x, y); conclusion = -(2x^2 - xy - yx + 2y^2)
    //                          = -2x^2 + 2xy - 2y^2.
    let tx = b.term(&v(0));
    let ty = b.term(&v(1));
    b.field(
        "PPsdCertT/term",
        vec![Body::nat(0), Body::lref(node)],
        Body::lref(tx),
    );
    b.field(
        "PPsdCertT/term",
        vec![Body::nat(1), Body::lref(node)],
        Body::lref(ty),
    );
    let concl_good = add(
        add(mul(c(-2), mul(v(0), v(0))), mul(c(2), mul(v(0), v(1)))),
        mul(c(-2), mul(v(1), v(1))),
    );
    let concl_bad = add(
        add(mul(c(-2), mul(v(0), v(0))), mul(c(2), mul(v(0), v(1)))),
        mul(c(-1), mul(v(1), v(1))),
    );
    let cg = b.term(&concl_good);
    let cb = b.term(&concl_bad);
    b.field(
        "PPsdCertT/conclusion",
        vec![Body::lref(node)],
        Body::lref(cg),
    );
    let rows = b.rows();
    assert_eq!(ev_elems("psdCertTConcl", &[node], &rows), Ok(true));
    // Re-point the conclusion at the mutant (fresh body: single-valued
    // field discipline — two conclusion rows would refuse).
    let mut b2 = Body::new();
    let node2 = psd_t_node(&mut b2, None);
    let tx2 = b2.term(&v(0));
    let ty2 = b2.term(&v(1));
    b2.field(
        "PPsdCertT/term",
        vec![Body::nat(0), Body::lref(node2)],
        Body::lref(tx2),
    );
    b2.field(
        "PPsdCertT/term",
        vec![Body::nat(1), Body::lref(node2)],
        Body::lref(ty2),
    );
    let cb2 = b2.term(&concl_bad);
    let _ = cb;
    b2.field(
        "PPsdCertT/conclusion",
        vec![Body::lref(node2)],
        Body::lref(cb2),
    );
    let rows2 = b2.rows();
    assert_eq!(ev_elems("psdCertTConcl", &[node2], &rows2), Ok(false));
}

#[test]
fn psd_cert_dd_witness() {
    let mut b = Body::new();
    // A = [[2,-1],[-1,2]], Z = I → B = A; strict dominance: 2 > |-1|.
    let node = b.elta("PPsdCertDD");
    b.field("PPsdCertDD/n", vec![Body::lref(node)], Body::nat(2));
    b.field(
        "PPsdCertDD/A",
        vec![Body::lref(node)],
        Body::q_tensor(&[2, 2], &[(2, 1), (-1, 1), (-1, 1), (2, 1)]),
    );
    b.field(
        "PPsdCertDD/Z",
        vec![Body::lref(node)],
        Body::q_tensor(&[2, 2], &[(1, 1), (0, 1), (0, 1), (1, 1)]),
    );
    // NOT strictly dominant: A = [[1,-1],[-1,1]] (singular).
    let node_bad = b.elta("PPsdCertDD");
    b.field("PPsdCertDD/n", vec![Body::lref(node_bad)], Body::nat(2));
    b.field(
        "PPsdCertDD/A",
        vec![Body::lref(node_bad)],
        Body::q_tensor(&[2, 2], &[(1, 1), (-1, 1), (-1, 1), (1, 1)]),
    );
    b.field(
        "PPsdCertDD/Z",
        vec![Body::lref(node_bad)],
        Body::q_tensor(&[2, 2], &[(1, 1), (0, 1), (0, 1), (1, 1)]),
    );
    let rows = b.rows();
    assert_eq!(ev_elems("psdCertDDWitness", &[node], &rows), Ok(true));
    assert_eq!(ev_elems("psdCertDDWitness", &[node_bad], &rows), Ok(false));
}

#[test]
fn psd_cert_k_witness() {
    // m = 1, k = 1, B = [2], N = [3] → L = (1 3),
    // A = L^T B L = [[2, 6], [6, 18]]; inner T witness Z = [1].
    let mut b = Body::new();
    let node = b.elta("PPsdCertK");
    b.field("PPsdCertK/m", vec![Body::lref(node)], Body::nat(1));
    b.field("PPsdCertK/k", vec![Body::lref(node)], Body::nat(1));
    b.field("PPsdCertK/nTotal", vec![Body::lref(node)], Body::nat(2));
    b.field(
        "PPsdCertK/A",
        vec![Body::lref(node)],
        Body::q_tensor(&[2, 2], &[(2, 1), (6, 1), (6, 1), (18, 1)]),
    );
    b.field(
        "PPsdCertK/N",
        vec![Body::lref(node)],
        Body::q_tensor(&[1, 1], &[(3, 1)]),
    );
    b.field(
        "PPsdCertK/B",
        vec![Body::lref(node)],
        Body::q_tensor(&[1, 1], &[(2, 1)]),
    );
    b.field(
        "PPsdCertK/innerT",
        vec![Body::lref(node)],
        Value::Lit(Literal::fin(1)),
    );
    b.field(
        "PPsdCertK/Z",
        vec![Body::lref(node)],
        Body::q_tensor(&[1, 1], &[(1, 1)]),
    );
    // Forged A entry.
    let node_bad = b.elta("PPsdCertK");
    b.field("PPsdCertK/m", vec![Body::lref(node_bad)], Body::nat(1));
    b.field("PPsdCertK/k", vec![Body::lref(node_bad)], Body::nat(1));
    b.field("PPsdCertK/nTotal", vec![Body::lref(node_bad)], Body::nat(2));
    b.field(
        "PPsdCertK/A",
        vec![Body::lref(node_bad)],
        Body::q_tensor(&[2, 2], &[(2, 1), (6, 1), (6, 1), (17, 1)]),
    );
    b.field(
        "PPsdCertK/N",
        vec![Body::lref(node_bad)],
        Body::q_tensor(&[1, 1], &[(3, 1)]),
    );
    b.field(
        "PPsdCertK/B",
        vec![Body::lref(node_bad)],
        Body::q_tensor(&[1, 1], &[(2, 1)]),
    );
    b.field(
        "PPsdCertK/innerT",
        vec![Body::lref(node_bad)],
        Value::Lit(Literal::fin(1)),
    );
    b.field(
        "PPsdCertK/Z",
        vec![Body::lref(node_bad)],
        Body::q_tensor(&[1, 1], &[(1, 1)]),
    );
    // nTotal lie.
    let node_tie = b.elta("PPsdCertK");
    b.field("PPsdCertK/m", vec![Body::lref(node_tie)], Body::nat(1));
    b.field("PPsdCertK/k", vec![Body::lref(node_tie)], Body::nat(1));
    b.field("PPsdCertK/nTotal", vec![Body::lref(node_tie)], Body::nat(3));
    let rows = b.rows();
    assert_eq!(ev_elems("psdCertKWitness", &[node], &rows), Ok(true));
    assert_eq!(ev_elems("psdCertKWitness", &[node_bad], &rows), Ok(false));
    assert_eq!(ev_elems("psdCertKWitness", &[node_tie], &rows), Ok(false));
}

// ---------------------------------------------------------------------
// positiveSizeWires / constExactEvalTrue
// ---------------------------------------------------------------------

#[test]
fn positive_size_wires_battery() {
    let mut b = Body::new();
    b.type_wire(0, &[1]); // positive
    b.type_wire(1, &[2, 3]); // positive
    b.type_wire(2, &[0]); // ZERO size — the B14 counterexample class
    let good_t = b.term(&add(v(0), v(1)));
    let bad_t = b.term(&add(v(0), v(2)));
    let good_f = b.formula(&atom(1, v(1), c(0)));
    let bad_f = b.formula(&atom(1, v(2), c(0)));
    let empty_f = b.formula(&F::True);
    let rows = b.rows();
    // positiveSizeWires field order: conclusion, pre.
    assert_eq!(
        ev_elems("positiveSizeWires", &[good_t, good_f], &rows),
        Ok(true)
    );
    assert_eq!(
        ev_elems("positiveSizeWires", &[good_t, bad_f], &rows),
        Ok(false)
    );
    assert_eq!(
        ev_elems("positiveSizeWires", &[bad_t, good_f], &rows),
        Ok(false)
    );
    assert_eq!(
        ev_elems("positiveSizeWiresTerm", &[good_t], &rows),
        Ok(true)
    );
    assert_eq!(
        ev_elems("positiveSizeWiresTerm", &[bad_t], &rows),
        Ok(false)
    );
    assert_eq!(
        ev_elems("positiveSizeWiresForm", &[bad_f], &rows),
        Ok(false)
    );
    assert_eq!(
        ev_elems("positiveSizeWiresForm", &[empty_f], &rows),
        Ok(true),
        "empty free-wire sweep is vacuously true"
    );
}

#[test]
fn const_exact_eval_battery() {
    let mut b = Body::new();
    let l = b.term(&T::Const(3, 2));
    let r = b.term(&c(2));
    let open = b.term(&v(0));
    // A closed COMPOSITE: (1/2)*4 - 1 = 1.
    let comp = b.term(&sub(mul(T::Const(1, 2), c(4)), c(1)));
    let one = b.term(&c(1));
    let rows = b.rows();
    let bt = |n: u64| Value::Lit(Literal::nat(n));
    let e = |bow: &Value, a: u32, bb: u32| {
        ev(
            "constExactEvalTrue",
            &[bow, &Body::lref(a), &Body::lref(bb)],
            &rows,
        )
    };
    assert_eq!(e(&bt(1), l, r), Ok(true)); // 3/2 <= 2
    assert_eq!(e(&bt(0), l, r), Ok(true)); // 3/2 < 2
    assert_eq!(e(&bt(3), l, r), Ok(false)); // 3/2 >= 2 — false
    assert_eq!(e(&bt(2), comp, one), Ok(true)); // (1/2)*4 - 1 = 1
    assert_eq!(e(&bt(2), l, r), Ok(false));
    assert_eq!(
        e(&bt(5), l, r),
        Ok(false),
        "bowtie 5 (NE) decidedly false — notNE"
    );
    assert_eq!(
        e(&bt(1), open, r),
        Ok(false),
        "open term is not closed — false"
    );
}
