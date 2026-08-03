//! The predicate semantic-class family exercised end to end through
//! provider dispatch: `isConicPredicate` / `isConvexPredicate` /
//! `isUpwardClosedConicPredicate` — spec battery (expected verdicts
//! from the Lean catalogue's `classifyPred`), named data mutants
//! (every mutant flips a verdict), refusal witnesses for each
//! unresolvable-structure class, and the frozen cross-implementation
//! corpus replay.
//!
//! The test-side row emitter shares no code with the evaluators: it
//! writes `Op::Elta`/`Op::Funa` rows directly from the synthetic
//! declaration index.

mod common;

use common::{ev_elems, stack, STACK};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use serde_json::Value as J;
use std::collections::HashMap;

// ---------------------------------------------------------------------
// Little ASTs (the surgery/promise batteries', predicate-sized)
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

fn c(n: i64) -> T {
    T::Const(n, 1)
}
fn hole() -> T {
    T::Hole
}
fn mul(l: T, r: T) -> T {
    T::Mul(Box::new(l), Box::new(r))
}
fn add(l: T, r: T) -> T {
    T::Add(Box::new(l), Box::new(r))
}
fn sub(l: T, r: T) -> T {
    T::Sub(Box::new(l), Box::new(r))
}
fn neg(t: T) -> T {
    T::Neg(Box::new(t))
}
fn atom(b: u8, l: T, r: T) -> F {
    F::Atom(b, l, r)
}
fn fand(l: F, r: F) -> F {
    F::And(Box::new(l), Box::new(r))
}
fn forr(l: F, r: F) -> F {
    F::Or(Box::new(l), Box::new(r))
}

// Bowtie codes (the design source).
const LT: u8 = 0;
const LE: u8 = 1;
const EQ: u8 = 2;
const GE: u8 = 3;
const GT: u8 = 4;
const NE: u8 = 5;

const ATOM_CTORS: [&str; 6] = [
    "FAtomLT", "FAtomLE", "FAtomEQ", "FAtomGE", "FAtomGT", "FAtomNE",
];

const RELS: [&str; 3] = [
    "isConicPredicate",
    "isConvexPredicate",
    "isUpwardClosedConicPredicate",
];

// ---------------------------------------------------------------------
// The test-side row emitter
// ---------------------------------------------------------------------

const OWN: [u8; 32] = [0xEC; 32];

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
        ] {
            fun.insert(name, s.fun(name).expect(name).chid);
        }
        let mut sort = HashMap::new();
        for name in ["Term", "Formula", "Wire", "Simplex", "ExtensionSet"] {
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

    /// A raw constructor row on an EXISTING element (refusal and
    /// ambiguity material).
    fn row(&mut self, fun: &'static str, args: Vec<Value>, value: Value) {
        self.ops.push(Op::Funa {
            fun: self.ext_ref(self.fun[fun]),
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
                self.ctor(
                    "Term",
                    "TIdx",
                    vec![Value::Lit(Literal::nat(*i)), Self::lref(xe)],
                )
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

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

/// All three verdicts for one predicate formula, through dispatch.
fn verdicts(f: &F) -> [Result<bool, String>; 3] {
    let mut b = Body::new();
    let fe = b.formula(f);
    let rows = b.rows();
    RELS.map(|name| ev_elems(name, &[fe], &rows))
}

/// Decided-verdict helper: all three must DECIDE (no refusal).
fn decided(label: &str, f: &F) -> [bool; 3] {
    verdicts(f).map(|r| r.unwrap_or_else(|e| panic!("`{label}` refused: {e}")))
}

// ---------------------------------------------------------------------
// Spec battery — expected verdicts transcribed from the Lean
// classifier ([conic, convex, upward-closed-conic] per row).
// ---------------------------------------------------------------------

#[test]
fn spec_battery() {
    let cases: Vec<(&str, F, [bool; 3])> = vec![
        // The v1 grammar rows, hole on the left.
        (
            "P1 workhorse: hole >= 0",
            atom(GE, hole(), c(0)),
            [true, true, true],
        ),
        (
            "P2 downward ray: hole <= 0",
            atom(LE, hole(), c(0)),
            [true, true, false],
        ),
        (
            "P3 kernel: hole = 0",
            atom(EQ, hole(), c(0)),
            [true, true, false],
        ),
        (
            "P4 scaled left: 3*hole >= 0",
            atom(GE, mul(c(3), hole()), c(0)),
            [true, true, true],
        ),
        (
            "P4 scaled right: hole*3 >= 0",
            atom(GE, mul(hole(), c(3)), c(0)),
            [true, true, true],
        ),
        (
            "P4 rational scale: (2/5)*hole >= 0",
            atom(GE, mul(T::Const(2, 5), hole()), c(0)),
            [true, true, true],
        ),
        (
            "scaled kernel: 2*hole = 0",
            atom(EQ, mul(c(2), hole()), c(0)),
            [true, true, false],
        ),
        (
            "scaled P2: 7*hole <= 0",
            atom(LE, mul(c(7), hole()), c(0)),
            [true, true, false],
        ),
        (
            "P5 shifted: hole >= 5",
            atom(GE, hole(), c(5)),
            [false, true, false],
        ),
        (
            "P6 shifted: hole <= 5",
            atom(LE, hole(), c(5)),
            [false, true, false],
        ),
        (
            "P5 negative shift: hole >= -3",
            atom(GE, hole(), c(-3)),
            [false, true, false],
        ),
        // Orientation flips (constant on the left re-orients the bowtie).
        (
            "flipped P1: 0 <= hole",
            atom(LE, c(0), hole()),
            [true, true, true],
        ),
        (
            "flipped P2: 0 >= hole",
            atom(GE, c(0), hole()),
            [true, true, false],
        ),
        (
            "flipped P5: 5 <= hole",
            atom(LE, c(5), hole()),
            [false, true, false],
        ),
        (
            "flipped kernel: 0 = hole",
            atom(EQ, c(0), hole()),
            [true, true, false],
        ),
        (
            "flipped scaled: 0 <= 2*hole",
            atom(LE, c(0), mul(c(2), hole())),
            [true, true, true],
        ),
        // evalQ? folding on the comparison side.
        (
            "folded zero: hole >= (1 - 1)",
            atom(GE, hole(), sub(c(1), c(1))),
            [true, true, true],
        ),
        (
            "folded zero via neg: hole >= -(0)",
            atom(GE, hole(), neg(c(0))),
            [true, true, true],
        ),
        (
            "folded nonzero: hole >= 2*3",
            atom(GE, hole(), mul(c(2), c(3))),
            [false, true, false],
        ),
        (
            "folded nested: hole <= (2 - (1 + 1))",
            atom(LE, hole(), sub(c(2), add(c(1), c(1)))),
            [true, true, false],
        ),
        // Outside the fragment: singleton off the origin.
        (
            "eq off origin: hole = 5",
            atom(EQ, hole(), c(5)),
            [false, false, false],
        ),
        // Outside: strict rays and disequality.
        (
            "strict: hole > 0",
            atom(GT, hole(), c(0)),
            [false, false, false],
        ),
        (
            "strict: hole < 0",
            atom(LT, hole(), c(0)),
            [false, false, false],
        ),
        (
            "diseq: hole != 0",
            atom(NE, hole(), c(0)),
            [false, false, false],
        ),
        // Outside: bad scalings (strict positivity, literal-only).
        (
            "zero scale: 0*hole >= 0",
            atom(GE, mul(c(0), hole()), c(0)),
            [false, false, false],
        ),
        (
            "negative scale: -2*hole >= 0",
            atom(GE, mul(c(-2), hole()), c(0)),
            [false, false, false],
        ),
        (
            "computed coefficient: (1+1)*hole >= 0",
            atom(GE, mul(add(c(1), c(1)), hole()), c(0)),
            [false, false, false],
        ),
        (
            "neg-literal coefficient: (-(2))*hole >= 0",
            atom(GE, mul(neg(c(2)), hole()), c(0)),
            [false, false, false],
        ),
        (
            "nested scale: 2*(3*hole) >= 0",
            atom(GE, mul(c(2), mul(c(3), hole())), c(0)),
            [false, false, false],
        ),
        // Outside: the constant side must fold under evalQ? — the
        // polynomial fold would accept these two.
        (
            "var-poisoned zero: hole >= 0*w7",
            atom(GE, hole(), mul(c(0), T::Var(7))),
            [false, false, false],
        ),
        (
            "idx-poisoned: hole >= idx(0)",
            atom(GE, hole(), T::Idx(0, Box::new(c(0)))),
            [false, false, false],
        ),
        // Outside: genuine wires (the hole-only condition is the
        // recognizer itself).
        (
            "real wire: w3 >= 0",
            atom(GE, T::Var(3), c(0)),
            [false, false, false],
        ),
        (
            "real wire scaled: 2*w3 >= 0",
            atom(GE, mul(c(2), T::Var(3)), c(0)),
            [false, false, false],
        ),
        // Outside: no orientation resolves.
        (
            "both holes: hole >= hole",
            atom(GE, hole(), hole()),
            [false, false, false],
        ),
        (
            "hole vs scaled hole: hole >= 2*hole",
            atom(GE, hole(), mul(c(2), hole())),
            [false, false, false],
        ),
        (
            "closed atom: 5 >= 3",
            atom(GE, c(5), c(3)),
            [false, false, false],
        ),
        (
            "idx of hole: idx(hole) >= 0",
            atom(GE, T::Idx(1, Box::new(hole())), c(0)),
            [false, false, false],
        ),
        // Conjunctions (P7 / P8).
        (
            "P7 conic pair: hole>=0 and hole<=0",
            fand(atom(GE, hole(), c(0)), atom(LE, hole(), c(0))),
            [true, true, false],
        ),
        (
            "P7 up-closed pair: hole>=0 and 3*hole>=0",
            fand(atom(GE, hole(), c(0)), atom(GE, mul(c(3), hole()), c(0))),
            [true, true, true],
        ),
        (
            "P8 slab: hole>=1 and hole<=5",
            fand(atom(GE, hole(), c(1)), atom(LE, hole(), c(5))),
            [false, true, false],
        ),
        (
            "mixed conic+shift: hole>=0 and hole<=5",
            fand(atom(GE, hole(), c(0)), atom(LE, hole(), c(5))),
            [false, true, false],
        ),
        (
            "nested and: ((hole>=0 and hole>=0) and hole>=0)",
            fand(
                fand(atom(GE, hole(), c(0)), atom(GE, hole(), c(0))),
                atom(GE, hole(), c(0)),
            ),
            [true, true, true],
        ),
        (
            "and with strict leaf: hole>=0 and hole>0",
            fand(atom(GE, hole(), c(0)), atom(GT, hole(), c(0))),
            [false, false, false],
        ),
        (
            "and with tt leaf: hole>=0 and tt",
            fand(atom(GE, hole(), c(0)), F::True),
            [false, false, false],
        ),
        // Non-atom leaves — the closed world.
        ("tt alone is not convex", F::True, [false, false, false]),
        ("ff alone", F::False, [false, false, false]),
        (
            "or of conic rays",
            forr(atom(GE, hole(), c(0)), atom(LE, hole(), c(0))),
            [false, false, false],
        ),
        (
            "inRegion leaf",
            F::InRegion(0, 0, hole()),
            [false, false, false],
        ),
        (
            "and over inRegion",
            fand(atom(GE, hole(), c(0)), F::InRegion(1, 1, T::Var(2))),
            [false, false, false],
        ),
    ];
    for (label, f, want) in &cases {
        let got = decided(label, f);
        assert_eq!(got, *want, "`{label}`: [conic, convex, upClosedConic]");
    }
}

// ---------------------------------------------------------------------
// Named data mutants — each flips at least one named verdict against
// its base. (The convex/conic split rows also witness the registry's
// shared-comment adjudication: convex is recognizer acceptance,
// strictly weaker than the conic bit.)
// ---------------------------------------------------------------------

#[test]
fn mutant_battery() {
    // (label, base, mutant, relation index whose verdict must flip
    // true -> false)
    let mutants: Vec<(&str, F, F, usize)> = vec![
        (
            "bowtie ge -> gt kills conic",
            atom(GE, hole(), c(0)),
            atom(GT, hole(), c(0)),
            0,
        ),
        (
            "constant 0 -> 1 kills conic (convex survives: the split)",
            atom(GE, hole(), c(0)),
            atom(GE, hole(), c(1)),
            0,
        ),
        (
            "ge -> le kills upward closure (conic survives)",
            atom(GE, hole(), c(0)),
            atom(LE, hole(), c(0)),
            2,
        ),
        (
            "coefficient 3 -> -3 kills convex",
            atom(GE, mul(c(3), hole()), c(0)),
            atom(GE, mul(c(-3), hole()), c(0)),
            1,
        ),
        (
            "hole -> real wire kills convex",
            atom(GE, hole(), c(0)),
            atom(GE, T::Var(9), c(0)),
            1,
        ),
        (
            "literal coefficient -> computed kills convex",
            atom(GE, mul(c(2), hole()), c(0)),
            atom(GE, mul(add(c(1), c(1)), hole()), c(0)),
            1,
        ),
        (
            "folded const -> var-poisoned kills convex",
            atom(GE, hole(), sub(c(1), c(1))),
            atom(GE, hole(), mul(c(0), T::Var(7))),
            1,
        ),
        (
            "conjunct tt-swap kills convex",
            fand(atom(GE, hole(), c(0)), atom(LE, hole(), c(0))),
            fand(atom(GE, hole(), c(0)), F::True),
            1,
        ),
        (
            "shifting one conjunct kills conic",
            fand(atom(GE, hole(), c(0)), atom(LE, hole(), c(0))),
            fand(atom(GE, hole(), c(0)), atom(LE, hole(), c(5))),
            0,
        ),
        (
            "and -> or kills convex",
            fand(atom(GE, hole(), c(0)), atom(LE, hole(), c(0))),
            forr(atom(GE, hole(), c(0)), atom(LE, hole(), c(0))),
            1,
        ),
    ];
    for (label, base, mutant, rel) in &mutants {
        let vb = decided(&format!("{label} (base)"), base);
        let vm = decided(&format!("{label} (mutant)"), mutant);
        assert!(vb[*rel], "`{label}`: base must hold on {}", RELS[*rel]);
        assert!(
            !vm[*rel],
            "`{label}`: mutant must flip {} to false",
            RELS[*rel]
        );
    }
}

// ---------------------------------------------------------------------
// Refusal witnesses — unresolvable structure, one per class.
// ---------------------------------------------------------------------

fn expect_refusal(label: &str, fe: u32, rows: &CertRows) {
    for name in RELS {
        let r = ev_elems(name, &[fe], rows);
        assert!(r.is_err(), "`{label}`: {name} must refuse, got {r:?}");
    }
}

#[test]
fn refusal_sph_leaf() {
    let mut b = Body::new();
    let fe = b.formula(&F::SpH);
    expect_refusal("bare spec-hole formula", fe, &b.rows());
}

#[test]
fn refusal_sph_under_conjunction() {
    let mut b = Body::new();
    let fe = b.formula(&fand(atom(GE, hole(), c(0)), F::SpH));
    expect_refusal("spec-hole conjunct", fe, &b.rows());
}

#[test]
fn refusal_unconstructed_formula() {
    let mut b = Body::new();
    let fe = b.elta("Formula");
    expect_refusal("formula element with no constructor row", fe, &b.rows());
}

#[test]
fn refusal_ambiguous_formula_ctor() {
    let mut b = Body::new();
    let fe = b.elta("Formula");
    b.row("FTrue", vec![], Body::lref(fe));
    b.row("FFalse", vec![], Body::lref(fe));
    expect_refusal("doubly-constructed formula element", fe, &b.rows());
}

#[test]
fn refusal_unconstructed_term() {
    let mut b = Body::new();
    let te = b.elta("Term");
    let ze = b.term(&c(0));
    let fe = b.ctor("Formula", "FAtomGE", vec![Body::lref(te), Body::lref(ze)]);
    expect_refusal("atom over an unconstructed term", fe, &b.rows());
}

#[test]
fn refusal_nonliteral_const() {
    let mut b = Body::new();
    // A TConst row whose argument is an element ref, not a literal.
    let he = b.term(&hole());
    let bad = b.elta("Term");
    b.row("TConst", vec![Body::lref(he)], Body::lref(bad));
    let fe = b.ctor("Formula", "FAtomGE", vec![Body::lref(he), Body::lref(bad)]);
    expect_refusal("TConst with a non-literal argument", fe, &b.rows());
}

#[test]
fn refusal_cyclic_conjunction() {
    let mut b = Body::new();
    let leaf = b.formula(&atom(GE, hole(), c(0)));
    let fe = b.elta("Formula");
    // FAnd(fe, leaf) constructing fe itself: a cyclic ∧-chain.
    b.row(
        "FAnd",
        vec![Body::lref(fe), Body::lref(leaf)],
        Body::lref(fe),
    );
    expect_refusal("cyclic conjunction chain", fe, &b.rows());
}

#[test]
fn refusal_non_element_argument() {
    let b = Body::new();
    let rows = b.rows();
    for name in RELS {
        let lit = Value::Lit(Literal::nat(7));
        let r = common::ev(name, &[&lit], &rows);
        assert!(r.is_err(), "{name} must refuse a literal argument");
    }
}

// ---------------------------------------------------------------------
// Frozen cross-implementation corpus replay
// ---------------------------------------------------------------------

fn term_from_json(j: &J) -> T {
    let a = j.as_array().expect("term array");
    match a[0].as_str().expect("tag") {
        "var" => T::Var(a[1].as_u64().expect("wire") as u32),
        "const" => T::Const(a[1].as_i64().expect("num"), a[2].as_u64().expect("den")),
        "add" => add(term_from_json(&a[1]), term_from_json(&a[2])),
        "mul" => mul(term_from_json(&a[1]), term_from_json(&a[2])),
        "sub" => sub(term_from_json(&a[1]), term_from_json(&a[2])),
        "neg" => neg(term_from_json(&a[1])),
        "idx" => T::Idx(a[1].as_u64().expect("i"), Box::new(term_from_json(&a[2]))),
        "hole" => T::Hole,
        t => panic!("unknown term tag {t}"),
    }
}

fn formula_from_json(j: &J) -> F {
    let a = j.as_array().expect("formula array");
    match a[0].as_str().expect("tag") {
        "atom" => F::Atom(
            a[1].as_u64().expect("bowtie") as u8,
            term_from_json(&a[2]),
            term_from_json(&a[3]),
        ),
        "and" => fand(formula_from_json(&a[1]), formula_from_json(&a[2])),
        "or" => forr(formula_from_json(&a[1]), formula_from_json(&a[2])),
        "tt" => F::True,
        "ff" => F::False,
        t => panic!("unknown formula tag {t}"),
    }
}

#[test]
fn corpus_replay() {
    let raw = include_str!("fixtures/predclass_pyref_corpus.json");
    let corpus: J = serde_json::from_str(raw).expect("valid corpus JSON");
    let cases = corpus["cases"].as_array().expect("cases");
    assert!(cases.len() >= 200, "corpus size: got {}", cases.len());
    for (i, case) in cases.iter().enumerate() {
        let f = formula_from_json(&case["formula"]);
        let want = [
            case["conic"].as_bool().expect("conic"),
            case["convex"].as_bool().expect("convex"),
            case["upclosed"].as_bool().expect("upclosed"),
        ];
        let got = decided(&format!("corpus case {i}"), &f);
        assert_eq!(
            got, want,
            "corpus case {i} ({:?}): [conic, convex, upClosedConic]",
            case["formula"]
        );
    }
}
