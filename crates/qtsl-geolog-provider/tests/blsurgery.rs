//! The surgery family exercised end to end through provider dispatch:
//! `conjunctAt`/`conjReplace` (∧-tree path reads and writes over
//! `CtxPath` rows) and `substituteInFormula`/`applyPredicateToTerm`
//! (the substitution pair) — spec battery, named data mutants (every
//! mutant flips a verdict), refusals, and the frozen
//! cross-implementation corpus replay.
//!
//! The test-side row emitter shares no code with the evaluators: it
//! writes `Op::Elta`/`Op::Funa` constructor rows directly from the
//! synthetic declaration index. Expected verdicts in the hand battery
//! come straight from the Lean catalogue's definitions
//! (`conjGet?`/`conjReplace?`/`Formula.subst`/`applyPredicateToTerm`).

mod common;

use common::{ev_elems, stack, STACK};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use serde_json::Value as J;
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
    Idx(u64, Box<T>),
    Hole,
}

#[derive(Debug, Clone, PartialEq)]
enum F {
    Atom(u8, T, T),
    And(Box<F>, Box<F>),
    Or(Box<F>, Box<F>),
    True,
    False,
    SpH,
    /// Nominal geometry ids into the body's simplex/ext pools.
    InRegion(u32, u32, T),
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
fn mul(l: T, r: T) -> T {
    T::Mul(Box::new(l), Box::new(r))
}
fn neg(x: T) -> T {
    T::Neg(Box::new(x))
}
fn idx(i: u64, x: T) -> T {
    T::Idx(i, Box::new(x))
}
fn le(l: T, r: T) -> F {
    F::Atom(1, l, r)
}
fn eq(l: T, r: T) -> F {
    F::Atom(2, l, r)
}
fn fand(l: F, r: F) -> F {
    F::And(Box::new(l), Box::new(r))
}
fn for_(l: F, r: F) -> F {
    F::Or(Box::new(l), Box::new(r))
}

const ATOM_CTORS: [&str; 6] = [
    "FAtomLT", "FAtomLE", "FAtomEQ", "FAtomGE", "FAtomGT", "FAtomNE",
];

/// A path step: `false` = left, `true` = right (PathL / PathR).
type Path = Vec<bool>;

// ---------------------------------------------------------------------
// The test-side row emitter
// ---------------------------------------------------------------------

const OWN: [u8; 32] = [0xE7; 32];

struct Body {
    ops: Vec<Op>,
    deps: Vec<[u8; 32]>,
    fun: HashMap<&'static str, Chid>,
    sort: HashMap<&'static str, Chid>,
    wires: HashMap<u32, u32>,
    simplexes: HashMap<u32, u32>,
    exts: HashMap<u32, u32>,
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
            "THole",
            "FAtomLT",
            "FAtomLE",
            "FAtomEQ",
            "FAtomGE",
            "FAtomGT",
            "FAtomNE",
            "FAnd",
            "FOr",
            "FTrue",
            "FFalse",
            "FSpH",
            "FInRegion",
            "PathHere",
            "PathL",
            "PathR",
        ] {
            fun.insert(name, s.fun(name).expect(name).chid);
        }
        let mut sort = HashMap::new();
        for name in [
            "Term",
            "Formula",
            "Wire",
            "CtxPath",
            "Simplex",
            "ExtensionSet",
        ] {
            sort.insert(name, s.sort(name).expect(name));
        }
        Body {
            ops: Vec::new(),
            deps: vec![STACK],
            fun,
            sort,
            wires: HashMap::new(),
            simplexes: HashMap::new(),
            exts: HashMap::new(),
        }
    }

    fn ext_ref(&self, chid: Chid) -> ElemRef {
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
            sort: self.ext_ref(self.sort[sort]),
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
            fun: self.ext_ref(self.fun[fun]),
            args,
            value: Self::lref(e),
        });
        e
    }

    /// A raw constructor row producing an EXISTING element (mutant /
    /// ambiguity material).
    fn ctor_row_for(&mut self, fun: &'static str, args: Vec<Value>, elem: u32) {
        self.ops.push(Op::Funa {
            fun: self.ext_ref(self.fun[fun]),
            args,
            value: Self::lref(elem),
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

    fn simplex(&mut self, id: u32) -> u32 {
        if let Some(e) = self.simplexes.get(&id) {
            return *e;
        }
        let e = self.elta("Simplex");
        self.simplexes.insert(id, e);
        e
    }

    fn ext_set(&mut self, id: u32) -> u32 {
        if let Some(e) = self.exts.get(&id) {
            return *e;
        }
        let e = self.elta("ExtensionSet");
        self.exts.insert(id, e);
        e
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
            T::Add(l, r) => {
                let (le, re) = (self.term(l), self.term(r));
                self.ctor("Term", "TAdd", vec![Self::lref(le), Self::lref(re)])
            }
            T::Sub(l, r) => {
                let (le, re) = (self.term(l), self.term(r));
                self.ctor("Term", "TSub", vec![Self::lref(le), Self::lref(re)])
            }
            T::Mul(l, r) => {
                let (le, re) = (self.term(l), self.term(r));
                self.ctor("Term", "TMul", vec![Self::lref(le), Self::lref(re)])
            }
            T::Neg(x) => {
                let xe = self.term(x);
                self.ctor("Term", "TNeg", vec![Self::lref(xe)])
            }
            // field order bytewise: i, t.
            T::Idx(i, x) => {
                let xe = self.term(x);
                self.ctor("Term", "TIdx", vec![Self::nat(*i), Self::lref(xe)])
            }
            T::Hole => self.ctor("Term", "THole", vec![]),
        }
    }

    fn formula(&mut self, f: &F) -> u32 {
        match f {
            F::Atom(b, l, r) => {
                let (le, re) = (self.term(l), self.term(r));
                self.ctor(
                    "Formula",
                    ATOM_CTORS[*b as usize],
                    vec![Self::lref(le), Self::lref(re)],
                )
            }
            F::And(l, r) => {
                let (le, re) = (self.formula(l), self.formula(r));
                self.ctor("Formula", "FAnd", vec![Self::lref(le), Self::lref(re)])
            }
            F::Or(l, r) => {
                let (le, re) = (self.formula(l), self.formula(r));
                self.ctor("Formula", "FOr", vec![Self::lref(le), Self::lref(re)])
            }
            F::True => self.ctor("Formula", "FTrue", vec![]),
            F::False => self.ctor("Formula", "FFalse", vec![]),
            F::SpH => self.ctor("Formula", "FSpH", vec![]),
            // field order bytewise: S, simplex, t.
            F::InRegion(s_id, sx_id, t) => {
                let se = self.ext_set(*s_id);
                let sxe = self.simplex(*sx_id);
                let te = self.term(t);
                self.ctor(
                    "Formula",
                    "FInRegion",
                    vec![Self::lref(se), Self::lref(sxe), Self::lref(te)],
                )
            }
        }
    }

    /// A `CtxPath` chain, prefix-first (`steps[0]` = the OUTERMOST
    /// constructor): built inside-out from `PathHere`.
    fn path(&mut self, steps: &[bool]) -> u32 {
        let mut cur = self.ctor("CtxPath", "PathHere", vec![]);
        for step in steps.iter().rev() {
            let ctor = if *step { "PathR" } else { "PathL" };
            cur = self.ctor("CtxPath", ctor, vec![Self::lref(cur)]);
        }
        cur
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

fn evb(name: &str, elems: &[u32], b: &Body) -> Result<bool, String> {
    ev_elems(name, elems, &b.rows())
}

// ---------------------------------------------------------------------
// conjunctAt — form.conjGet? path = some sub
// ---------------------------------------------------------------------

#[test]
fn conjunct_at_here_is_the_whole_formula() {
    let mut b = Body::new();
    let f = fand(le(v(0), c(1)), F::True);
    let form = b.formula(&f);
    let path = b.path(&[]);
    let sub = b.formula(&f); // struct-equal, distinct elements
    assert_eq!(evb("conjunctAt", &[form, path, sub], &b), Ok(true));
}

#[test]
fn conjunct_at_depth_two_reads_each_leaf() {
    // form = (a ∧ b) ∧ c; [L,L] → a, [L,R] → b, [R] → c.
    let a = le(v(0), c(0));
    let bb = eq(v(1), c(2));
    let cc = F::True;
    let f = fand(fand(a.clone(), bb.clone()), cc.clone());
    for (steps, leaf) in [
        (vec![false, false], &a),
        (vec![false, true], &bb),
        (vec![true], &cc),
    ] {
        let mut b = Body::new();
        let form = b.formula(&f);
        let path = b.path(&steps);
        let sub = b.formula(leaf);
        assert_eq!(
            evb("conjunctAt", &[form, path, sub], &b),
            Ok(true),
            "path {steps:?}"
        );
    }
}

#[test]
fn conjunct_at_interior_node_is_a_conjunct() {
    // conjGet? at an interior ∧-node returns the whole subtree.
    let inner = fand(le(v(0), c(0)), F::True);
    let f = fand(inner.clone(), F::False);
    let mut b = Body::new();
    let form = b.formula(&f);
    let path = b.path(&[false]);
    let sub = b.formula(&inner);
    assert_eq!(evb("conjunctAt", &[form, path, sub], &b), Ok(true));
}

#[test]
fn conjunct_at_mutant_wrong_sub_fails() {
    let a = le(v(0), c(0));
    let f = fand(a, F::True);
    let mut b = Body::new();
    let form = b.formula(&f);
    let path = b.path(&[false]);
    let sub = b.formula(&le(v(0), c(1))); // the mutant: 0 → 1
    assert_eq!(evb("conjunctAt", &[form, path, sub], &b), Ok(false));
}

#[test]
fn conjunct_at_off_tree_path_fails() {
    // A left step at an atom: conjGet? = none — decidedly false.
    let mut b = Body::new();
    let form = b.formula(&le(v(0), c(1)));
    let path = b.path(&[false]);
    let sub = b.formula(&le(v(0), c(1)));
    assert_eq!(evb("conjunctAt", &[form, path, sub], &b), Ok(false));
}

#[test]
fn conjunct_at_off_tree_below_a_leaf_fails() {
    // [L] lands on an atom; [L,L] steps past it.
    let f = fand(le(v(0), c(1)), F::True);
    let mut b = Body::new();
    let form = b.formula(&f);
    let path = b.path(&[false, false]);
    let sub = b.formula(&le(v(0), c(1)));
    assert_eq!(evb("conjunctAt", &[form, path, sub], &b), Ok(false));
}

#[test]
fn conjunct_at_or_is_not_an_and_node() {
    // The path walks ∧-structure ONLY: a step at an FOr is off-tree.
    let f = for_(le(v(0), c(1)), F::True);
    let mut b = Body::new();
    let form = b.formula(&f);
    let path = b.path(&[false]);
    let sub = b.formula(&le(v(0), c(1)));
    assert_eq!(evb("conjunctAt", &[form, path, sub], &b), Ok(false));
}

#[test]
fn unconstructed_path_refuses() {
    let mut b = Body::new();
    let form = b.formula(&F::True);
    let ghost = b.elta("CtxPath"); // element, no constructor row
    let sub = b.formula(&F::True);
    let err = evb("conjunctAt", &[form, ghost, sub], &b).unwrap_err();
    assert!(
        err.contains("no roster constructor row"),
        "unconstructed path must refuse: {err}"
    );
}

#[test]
fn cyclic_path_refuses() {
    let mut b = Body::new();
    let form = b.formula(&F::True);
    let sub = b.formula(&F::True);
    // PathL(p) = p — a self-cycle.
    let p = b.elta("CtxPath");
    b.ctor_row_for("PathL", vec![Body::lref(p)], p);
    let err = evb("conjunctAt", &[form, p, sub], &b).unwrap_err();
    assert!(
        err.contains("cyclic"),
        "cyclic path chain must refuse: {err}"
    );
}

#[test]
fn ambiguous_path_constructor_refuses() {
    let mut b = Body::new();
    let form = b.formula(&F::True);
    let sub = b.formula(&F::True);
    let p = b.path(&[]);
    // A second roster row producing the same element.
    let here2 = b.path(&[]);
    b.ctor_row_for("PathL", vec![Body::lref(here2)], p);
    let err = evb("conjunctAt", &[form, p, sub], &b).unwrap_err();
    assert!(
        err.contains("multiple roster constructor rows"),
        "ambiguous path element must refuse: {err}"
    );
}

// ---------------------------------------------------------------------
// conjReplace — form.conjReplace? path sub = some result
// ---------------------------------------------------------------------

#[test]
fn conj_replace_left_arm() {
    let a = le(v(0), c(0));
    let keep = eq(v(1), c(2));
    let x = F::SpH;
    let mut b = Body::new();
    let form = b.formula(&fand(a, keep.clone()));
    let path = b.path(&[false]);
    let result = b.formula(&fand(x.clone(), keep));
    let sub = b.formula(&x);
    assert_eq!(evb("conjReplace", &[form, path, result, sub], &b), Ok(true));
}

#[test]
fn conj_replace_here_ignores_the_input_shape() {
    // conjReplace? .here g = some g even on a non-∧ input: only
    // result = sub is constrained.
    let mut b = Body::new();
    let form = b.formula(&le(v(0), c(1)));
    let path = b.path(&[]);
    let result = b.formula(&F::True);
    let sub = b.formula(&F::True);
    assert_eq!(evb("conjReplace", &[form, path, result, sub], &b), Ok(true));
}

#[test]
fn conj_replace_deep_right_left() {
    // form = a ∧ ((p ∧ q) ∧ r); replace at [R,L] (= p ∧ q).
    let a = le(v(0), c(0));
    let p = eq(v(1), c(1));
    let q = F::True;
    let r = F::False;
    let x = le(v(2), c(3));
    let mut b = Body::new();
    let form = b.formula(&fand(a.clone(), fand(fand(p, q), r.clone())));
    let path = b.path(&[true, false]);
    let result = b.formula(&fand(a, fand(x.clone(), r)));
    let sub = b.formula(&x);
    assert_eq!(evb("conjReplace", &[form, path, result, sub], &b), Ok(true));
}

#[test]
fn conj_replace_mutant_sibling_perturbed_fails() {
    let a = le(v(0), c(0));
    let keep = eq(v(1), c(2));
    let keep_mut = eq(v(1), c(3)); // the mutant: untouched arm changed
    let x = F::SpH;
    let mut b = Body::new();
    let form = b.formula(&fand(a, keep));
    let path = b.path(&[false]);
    let result = b.formula(&fand(x.clone(), keep_mut));
    let sub = b.formula(&x);
    assert_eq!(
        evb("conjReplace", &[form, path, result, sub], &b),
        Ok(false)
    );
}

#[test]
fn conj_replace_mutant_wrong_replacement_fails() {
    let a = le(v(0), c(0));
    let keep = eq(v(1), c(2));
    let mut b = Body::new();
    let form = b.formula(&fand(a, keep.clone()));
    let path = b.path(&[false]);
    let result = b.formula(&fand(F::False, keep)); // planted ≠ sub
    let sub = b.formula(&F::SpH);
    assert_eq!(
        evb("conjReplace", &[form, path, result, sub], &b),
        Ok(false)
    );
}

#[test]
fn conj_replace_off_tree_fails() {
    let mut b = Body::new();
    let form = b.formula(&le(v(0), c(1)));
    let path = b.path(&[false]);
    let result = b.formula(&F::True);
    let sub = b.formula(&F::True);
    assert_eq!(
        evb("conjReplace", &[form, path, result, sub], &b),
        Ok(false)
    );
}

#[test]
fn conj_replace_result_not_an_and_fails() {
    // The input descends an ∧ but the claimed output is an atom:
    // no `.and l' r` shape — decidedly false.
    let a = le(v(0), c(0));
    let mut b = Body::new();
    let form = b.formula(&fand(a, F::True));
    let path = b.path(&[false]);
    let result = b.formula(&le(v(2), c(2)));
    let sub = b.formula(&F::SpH);
    assert_eq!(
        evb("conjReplace", &[form, path, result, sub], &b),
        Ok(false)
    );
}

#[test]
fn conj_replace_result_may_share_the_untouched_arm() {
    // The output row-shares the untouched arm ELEMENT with the input
    // — struct_eq's identity short-circuit, legitimate row sharing.
    let x = F::SpH;
    let mut b = Body::new();
    let a_e = b.formula(&le(v(0), c(0)));
    let keep_e = b.formula(&eq(v(1), c(2)));
    let form = b.ctor("Formula", "FAnd", vec![Body::lref(a_e), Body::lref(keep_e)]);
    let sub = b.formula(&x);
    let result = b.ctor("Formula", "FAnd", vec![Body::lref(sub), Body::lref(keep_e)]);
    let path = b.path(&[false]);
    assert_eq!(evb("conjReplace", &[form, path, result, sub], &b), Ok(true));
}

// ---------------------------------------------------------------------
// substituteInFormula — result = form[TVar(wire) := term]
// ---------------------------------------------------------------------

/// Field order: form, result, term, wire (the registry's bytewise
/// order — NOT the theory declaration order).
fn subst_args(form: u32, result: u32, term: u32, wire: u32) -> [u32; 4] {
    [form, result, term, wire]
}

#[test]
fn subst_replaces_the_wire() {
    let mut b = Body::new();
    let form = b.formula(&le(v(0), c(1)));
    let term = b.term(&add(v(1), c(2)));
    let result = b.formula(&le(add(v(1), c(2)), c(1)));
    let wire = b.wire(0);
    assert_eq!(
        evb(
            "substituteInFormula",
            &subst_args(form, result, term, wire),
            &b
        ),
        Ok(true)
    );
}

#[test]
fn subst_replaces_every_occurrence() {
    let f = fand(le(v(0), mul(v(0), c(2))), eq(v(1), v(0)));
    let s = neg(c(3));
    let expected = fand(le(s.clone(), mul(s.clone(), c(2))), eq(v(1), s.clone()));
    let mut b = Body::new();
    let form = b.formula(&f);
    let term = b.term(&s);
    let result = b.formula(&expected);
    let wire = b.wire(0);
    assert_eq!(
        evb(
            "substituteInFormula",
            &subst_args(form, result, term, wire),
            &b
        ),
        Ok(true)
    );
}

#[test]
fn subst_mutant_one_occurrence_left_fails() {
    let f = fand(le(v(0), c(1)), eq(v(0), c(2)));
    let s = c(7);
    // The mutant: second occurrence left unsubstituted.
    let mutant = fand(le(c(7), c(1)), eq(v(0), c(2)));
    let mut b = Body::new();
    let form = b.formula(&f);
    let term = b.term(&s);
    let result = b.formula(&mutant);
    let wire = b.wire(0);
    assert_eq!(
        evb(
            "substituteInFormula",
            &subst_args(form, result, term, wire),
            &b
        ),
        Ok(false)
    );
}

#[test]
fn subst_preserves_other_wires() {
    let f = le(v(0), v(1));
    let expected = le(c(5), v(1));
    let mut b = Body::new();
    let form = b.formula(&f);
    let term = b.term(&c(5));
    let result = b.formula(&expected);
    let wire = b.wire(0);
    assert_eq!(
        evb(
            "substituteInFormula",
            &subst_args(form, result, term, wire),
            &b
        ),
        Ok(true)
    );
}

#[test]
fn subst_mutant_other_wire_also_replaced_fails() {
    let f = le(v(0), v(1));
    let mutant = le(c(5), c(5)); // v1 replaced too
    let mut b = Body::new();
    let form = b.formula(&f);
    let term = b.term(&c(5));
    let result = b.formula(&mutant);
    let wire = b.wire(0);
    assert_eq!(
        evb(
            "substituteInFormula",
            &subst_args(form, result, term, wire),
            &b
        ),
        Ok(false)
    );
}

#[test]
fn subst_descends_idx_and_neg() {
    // Lean: `.idx u i => .idx (subst u) i` — the term slot descends,
    // the index is preserved.
    let f = eq(idx(2, v(0)), neg(v(0)));
    let s = add(v(1), c(1));
    let expected = eq(idx(2, s.clone()), neg(s.clone()));
    let mut b = Body::new();
    let form = b.formula(&f);
    let term = b.term(&s);
    let result = b.formula(&expected);
    let wire = b.wire(0);
    assert_eq!(
        evb(
            "substituteInFormula",
            &subst_args(form, result, term, wire),
            &b
        ),
        Ok(true)
    );
}

#[test]
fn subst_identity_when_wire_absent_shares_elements() {
    // The wire does not occur: result may BE the form element.
    let f = fand(le(v(1), c(1)), F::SpH);
    let mut b = Body::new();
    let form = b.formula(&f);
    let term = b.term(&c(9));
    let wire = b.wire(0);
    assert_eq!(
        evb(
            "substituteInFormula",
            &subst_args(form, form, term, wire),
            &b
        ),
        Ok(true)
    );
}

#[test]
fn subst_self_var_is_identity() {
    // term = TVar(wire): substitution is the identity — the same
    // element may stand on both sides.
    let f = le(v(0), c(1));
    let mut b = Body::new();
    let form = b.formula(&f);
    let term = b.term(&v(0));
    let wire = b.wire(0);
    assert_eq!(
        evb(
            "substituteInFormula",
            &subst_args(form, form, term, wire),
            &b
        ),
        Ok(true)
    );
}

#[test]
fn subst_leaves_the_hole_alone() {
    // THole projects to `.var predicateHole`, which no genuine wire
    // substitution touches (`holeFresh`).
    let f = le(T::Hole, v(0));
    let expected = le(T::Hole, c(4));
    let mut b = Body::new();
    let form = b.formula(&f);
    let term = b.term(&c(4));
    let result = b.formula(&expected);
    let wire = b.wire(0);
    assert_eq!(
        evb(
            "substituteInFormula",
            &subst_args(form, result, term, wire),
            &b
        ),
        Ok(true)
    );
}

#[test]
fn subst_mutant_hole_replaced_fails() {
    let f = le(T::Hole, v(0));
    let mutant = le(c(4), c(4)); // the hole substituted too
    let mut b = Body::new();
    let form = b.formula(&f);
    let term = b.term(&c(4));
    let result = b.formula(&mutant);
    let wire = b.wire(0);
    assert_eq!(
        evb(
            "substituteInFormula",
            &subst_args(form, result, term, wire),
            &b
        ),
        Ok(false)
    );
}

#[test]
fn subst_in_region_preserves_nominal_geometry() {
    // Lean: `.inRegion u simplex S => .inRegion (subst u) simplex S`.
    let f = F::InRegion(0, 0, v(0));
    let expected = F::InRegion(0, 0, c(2));
    let mut b = Body::new();
    let form = b.formula(&f);
    let term = b.term(&c(2));
    let result = b.formula(&expected);
    let wire = b.wire(0);
    assert_eq!(
        evb(
            "substituteInFormula",
            &subst_args(form, result, term, wire),
            &b
        ),
        Ok(true)
    );
}

#[test]
fn subst_mutant_in_region_geometry_swapped_fails() {
    let f = F::InRegion(0, 0, v(0));
    let mutant = F::InRegion(0, 1, c(2)); // different simplex element
    let mut b = Body::new();
    let form = b.formula(&f);
    let term = b.term(&c(2));
    let result = b.formula(&mutant);
    let wire = b.wire(0);
    assert_eq!(
        evb(
            "substituteInFormula",
            &subst_args(form, result, term, wire),
            &b
        ),
        Ok(false)
    );
}

#[test]
fn subst_wire_argument_must_be_a_ref() {
    let mut b = Body::new();
    let form = b.formula(&F::True);
    let term = b.term(&c(1));
    let vals = [
        Body::lref(form),
        Body::lref(form),
        Body::lref(term),
        Body::nat(0),
    ];
    let refs: Vec<&Value> = vals.iter().collect();
    let err = common::ev("substituteInFormula", &refs, &b.rows()).unwrap_err();
    assert!(
        err.contains("element ref"),
        "literal wire must refuse: {err}"
    );
}

#[test]
fn subst_unconstructed_form_refuses() {
    let mut b = Body::new();
    let ghost = b.elta("Formula");
    let term = b.term(&c(1));
    let wire = b.wire(0);
    let err = evb(
        "substituteInFormula",
        &subst_args(ghost, ghost, term, wire),
        &b,
    )
    .unwrap_err();
    assert!(
        err.contains("no roster constructor row"),
        "unconstructed formula must refuse: {err}"
    );
}

// ---------------------------------------------------------------------
// applyPredicateToTerm — result = predicate[THole := arg]
// ---------------------------------------------------------------------

/// Field order: arg, predicate, result.
fn apply_args(arg: u32, predicate: u32, result: u32) -> [u32; 3] {
    [arg, predicate, result]
}

#[test]
fn apply_fills_the_hole() {
    let p = le(T::Hole, c(0));
    let a = mul(v(0), v(0));
    let expected = le(a.clone(), c(0));
    let mut b = Body::new();
    let arg = b.term(&a);
    let pred = b.formula(&p);
    let result = b.formula(&expected);
    assert_eq!(
        evb("applyPredicateToTerm", &apply_args(arg, pred, result), &b),
        Ok(true)
    );
}

#[test]
fn apply_fills_every_hole() {
    let p = fand(le(T::Hole, c(1)), eq(neg(T::Hole), idx(1, T::Hole)));
    let a = add(v(0), c(2));
    let expected = fand(le(a.clone(), c(1)), eq(neg(a.clone()), idx(1, a.clone())));
    let mut b = Body::new();
    let arg = b.term(&a);
    let pred = b.formula(&p);
    let result = b.formula(&expected);
    assert_eq!(
        evb("applyPredicateToTerm", &apply_args(arg, pred, result), &b),
        Ok(true)
    );
}

#[test]
fn apply_mutant_hole_left_fails() {
    let p = fand(le(T::Hole, c(1)), eq(T::Hole, c(2)));
    let a = v(0);
    let mutant = fand(le(v(0), c(1)), eq(T::Hole, c(2))); // one hole left
    let mut b = Body::new();
    let arg = b.term(&a);
    let pred = b.formula(&p);
    let result = b.formula(&mutant);
    assert_eq!(
        evb("applyPredicateToTerm", &apply_args(arg, pred, result), &b),
        Ok(false)
    );
}

#[test]
fn apply_leaves_wires_alone() {
    let p = le(add(T::Hole, v(1)), v(2));
    let a = c(3);
    let expected = le(add(c(3), v(1)), v(2));
    let mut b = Body::new();
    let arg = b.term(&a);
    let pred = b.formula(&p);
    let result = b.formula(&expected);
    assert_eq!(
        evb("applyPredicateToTerm", &apply_args(arg, pred, result), &b),
        Ok(true)
    );
}

#[test]
fn apply_mutant_wrong_argument_fails() {
    let p = le(T::Hole, c(0));
    let mut b = Body::new();
    let arg = b.term(&v(0));
    let pred = b.formula(&p);
    let result = b.formula(&le(v(1), c(0))); // filled with v1, arg is v0
    assert_eq!(
        evb("applyPredicateToTerm", &apply_args(arg, pred, result), &b),
        Ok(false)
    );
}

#[test]
fn apply_holeless_predicate_is_identity() {
    let p = fand(le(v(0), c(1)), F::SpH);
    let mut b = Body::new();
    let arg = b.term(&c(9));
    let pred = b.formula(&p);
    // result may BE the predicate element.
    assert_eq!(
        evb("applyPredicateToTerm", &apply_args(arg, pred, pred), &b),
        Ok(true)
    );
}

#[test]
fn apply_hole_valued_argument_composes() {
    // arg itself contains a hole: the result carries it where the
    // predicate's holes were (single top-down substitution, exactly
    // `P.subst predicateHole arg`).
    let p = le(T::Hole, c(0));
    let a = add(T::Hole, c(1));
    let expected = le(add(T::Hole, c(1)), c(0));
    let mut b = Body::new();
    let arg = b.term(&a);
    let pred = b.formula(&p);
    let result = b.formula(&expected);
    assert_eq!(
        evb("applyPredicateToTerm", &apply_args(arg, pred, result), &b),
        Ok(true)
    );
}

// ---------------------------------------------------------------------
// Roster
// ---------------------------------------------------------------------

#[test]
fn provider_claims_all_four() {
    let p = common::provider();
    for name in [
        "applyPredicateToTerm",
        "conjReplace",
        "conjunctAt",
        "substituteInFormula",
    ] {
        assert!(p.local_by_name(name).is_some(), "`{name}` claimed");
    }
}

// ---------------------------------------------------------------------
// The frozen cross-implementation corpus (python AST arm): replay
// every instance through provider dispatch and require verdict
// agreement. Disagreement = stop-and-investigate, never
// adjust-the-corpus.
// ---------------------------------------------------------------------

fn corpus() -> J {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/surgery_pyref_corpus.json"
    );
    serde_json::from_str(&std::fs::read_to_string(path).expect("corpus present"))
        .expect("corpus parses")
}

fn jterm(j: &J) -> T {
    let a = j.as_array().expect("term node");
    match a[0].as_str().expect("tag") {
        "var" => T::Var(a[1].as_u64().expect("wire") as u32),
        "const" => T::Const(a[1].as_i64().expect("num"), a[2].as_u64().expect("den")),
        "add" => T::Add(Box::new(jterm(&a[1])), Box::new(jterm(&a[2]))),
        "mul" => T::Mul(Box::new(jterm(&a[1])), Box::new(jterm(&a[2]))),
        "sub" => T::Sub(Box::new(jterm(&a[1])), Box::new(jterm(&a[2]))),
        "neg" => T::Neg(Box::new(jterm(&a[1]))),
        "idx" => T::Idx(a[1].as_u64().expect("index"), Box::new(jterm(&a[2]))),
        "hole" => T::Hole,
        t => panic!("unknown term tag {t}"),
    }
}

fn jformula(j: &J) -> F {
    let a = j.as_array().expect("formula node");
    match a[0].as_str().expect("tag") {
        "atom" => F::Atom(
            a[1].as_u64().expect("bowtie") as u8,
            jterm(&a[2]),
            jterm(&a[3]),
        ),
        "and" => F::And(Box::new(jformula(&a[1])), Box::new(jformula(&a[2]))),
        "or" => F::Or(Box::new(jformula(&a[1])), Box::new(jformula(&a[2]))),
        "tt" => F::True,
        "ff" => F::False,
        "sph" => F::SpH,
        t => panic!("unknown formula tag {t}"),
    }
}

fn jpath(j: &J) -> Path {
    j.as_array()
        .expect("path")
        .iter()
        .map(|s| s.as_u64().expect("step") == 1)
        .collect()
}

#[test]
fn pyref_conjunct_at() {
    let c = corpus();
    let mut n = 0;
    for case in c["conjunct_at"].as_array().expect("list") {
        let mut b = Body::new();
        let form = b.formula(&jformula(&case["form"]));
        let path = b.path(&jpath(&case["path"]));
        let sub = b.formula(&jformula(&case["sub"]));
        assert_eq!(
            evb("conjunctAt", &[form, path, sub], &b),
            Ok(case["verdict"].as_bool().expect("verdict")),
            "conjunct_at case {n} disagrees with the python arm"
        );
        n += 1;
    }
    assert!(n >= 60, "corpus size");
}

#[test]
fn pyref_conj_replace() {
    let c = corpus();
    let mut n = 0;
    for case in c["conj_replace"].as_array().expect("list") {
        let mut b = Body::new();
        let form = b.formula(&jformula(&case["form"]));
        let path = b.path(&jpath(&case["path"]));
        let result = b.formula(&jformula(&case["result"]));
        let sub = b.formula(&jformula(&case["sub"]));
        assert_eq!(
            evb("conjReplace", &[form, path, result, sub], &b),
            Ok(case["verdict"].as_bool().expect("verdict")),
            "conj_replace case {n} disagrees with the python arm"
        );
        n += 1;
    }
    assert!(n >= 60, "corpus size");
}

#[test]
fn pyref_subst() {
    let c = corpus();
    let mut n = 0;
    for case in c["subst"].as_array().expect("list") {
        let mut b = Body::new();
        let form = b.formula(&jformula(&case["form"]));
        let result = b.formula(&jformula(&case["result"]));
        let term = b.term(&jterm(&case["term"]));
        let wire = b.wire(case["wire"].as_u64().expect("wire") as u32);
        assert_eq!(
            evb(
                "substituteInFormula",
                &subst_args(form, result, term, wire),
                &b
            ),
            Ok(case["verdict"].as_bool().expect("verdict")),
            "subst case {n} disagrees with the python arm"
        );
        n += 1;
    }
    assert!(n >= 60, "corpus size");
}

#[test]
fn pyref_apply_pred() {
    let c = corpus();
    let mut n = 0;
    for case in c["apply_pred"].as_array().expect("list") {
        let mut b = Body::new();
        let arg = b.term(&jterm(&case["arg"]));
        let pred = b.formula(&jformula(&case["pred"]));
        let result = b.formula(&jformula(&case["result"]));
        assert_eq!(
            evb("applyPredicateToTerm", &apply_args(arg, pred, result), &b),
            Ok(case["verdict"].as_bool().expect("verdict")),
            "apply_pred case {n} disagrees with the python arm"
        );
        n += 1;
    }
    assert!(n >= 60, "corpus size");
}
