//! `atomicCompareForm` / `atomicCompareZero`: the row-context
//! evaluation exercised end to end against an independent AST
//! reference — the tests build little Term/Formula trees, emit them as
//! certificate-body rows through a test-side emitter that shares no
//! code with the evaluator, and compare the evaluator's verdict
//! against plain structural equality on the ASTs. Interning is toggled
//! both ways: interned bodies exercise the identity short-circuit,
//! non-interned bodies the constructor-row recursion (pool dedup is
//! the writer's choice — the evaluator must not care).

mod common;

use common::{stack, STACK};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use geolog_ground_api::Verdict;
use proptest::prelude::*;
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use std::collections::HashMap;

// ---------------------------------------------------------------------
// The independent reference: little ASTs + structural predicates
// ---------------------------------------------------------------------

/// Reference terms. `Const` carries a CANONICAL (num, den) pair — the
/// [`cq`] smart constructor reduces, mirroring the envelope literal's
/// canonical form so AST equality and cell equality coincide.
#[derive(Debug, Clone, PartialEq, Eq)]
enum T {
    /// A wire, by test-local id — wires are NOMINAL (one element per
    /// id; distinct ids are distinct wires).
    Var(u32),
    Const(i64, u64),
    Add(Box<T>, Box<T>),
    Sub(Box<T>, Box<T>),
    Mul(Box<T>, Box<T>),
    Neg(Box<T>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum F {
    /// bowtie coding 0=LT 1=LE 2=EQ 3=GE 4=GT (the design source).
    Atom(u8, T, T),
    And(Box<F>, Box<F>),
    True,
}

fn cq(num: i64, den: u64) -> T {
    fn gcd(a: u64, b: u64) -> u64 {
        if b == 0 {
            a
        } else {
            gcd(b, a % b)
        }
    }
    let g = gcd(num.unsigned_abs(), den).max(1);
    T::Const(num / g as i64, den / g)
}

/// `atomicCompareForm`'s reference: formula IS `(l bowtie r)`.
fn form_ref(bowtie: u64, l: &T, r: &T, f: &F) -> bool {
    match f {
        F::Atom(b, fl, fr) => u64::from(*b) == bowtie && bowtie < 5 && fl == l && fr == r,
        _ => false,
    }
}

/// `atomicCompareZero`'s reference: formula IS `((l - r) bowtie 0)`.
fn zero_ref(bowtie: u64, l: &T, r: &T, f: &F) -> bool {
    let want = F::Atom(
        u8::try_from(bowtie).unwrap_or(u8::MAX),
        T::Sub(Box::new(l.clone()), Box::new(r.clone())),
        T::Const(0, 1),
    );
    bowtie < 5 && *f == want
}

// ---------------------------------------------------------------------
// The test-side row emitter (shares nothing with the oracle)
// ---------------------------------------------------------------------

const OWN: [u8; 32] = [0xCC; 32];

struct Body {
    ops: Vec<Op>,
    deps: Vec<[u8; 32]>,
    /// Stack constructor chids, resolved once by name (test-side name
    /// use — the oracle under test dispatches by pinned identity).
    fun: HashMap<&'static str, Chid>,
    term_sort: Chid,
    formula_sort: Chid,
    wire_sort: Chid,
    wires: HashMap<u32, u32>,
    /// Structural memo for interned emission (None = every subtree
    /// gets a fresh element).
    intern: Option<HashMap<String, u32>>,
}

impl Body {
    fn new(interned: bool) -> Body {
        let s = stack();
        let mut fun = HashMap::new();
        for name in [
            "TVar", "TConst", "TAdd", "TSub", "TMul", "TNeg", "FAtomLT", "FAtomLE", "FAtomEQ",
            "FAtomGE", "FAtomGT", "FAtomNE", "FAnd", "FTrue",
        ] {
            fun.insert(name, s.fun(name).expect("stack constructor").chid);
        }
        Body {
            ops: Vec::new(),
            deps: vec![STACK],
            fun,
            term_sort: s.sort("Term").expect("Term sort"),
            formula_sort: s.sort("Formula").expect("Formula sort"),
            wire_sort: s.sort("Wire").expect("Wire sort"),
            wires: HashMap::new(),
            intern: interned.then(HashMap::new),
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

    fn elta(&mut self, sort: Chid) -> u32 {
        let e = self.ops.len() as u32;
        self.ops.push(Op::Elta {
            sort: self.ext(sort),
        });
        e
    }

    /// Element + its constructor row.
    fn ctor(&mut self, sort: Chid, fun: &'static str, args: Vec<Value>) -> u32 {
        let e = self.elta(sort);
        self.ops.push(Op::Funa {
            fun: self.ext(self.fun[fun]),
            args,
            value: Value::Ref(ElemRef::Local(e)),
        });
        e
    }

    fn wire(&mut self, id: u32) -> u32 {
        if let Some(e) = self.wires.get(&id) {
            return *e;
        }
        let e = self.elta(self.wire_sort);
        self.wires.insert(id, e);
        e
    }

    fn memo(&mut self, key: String, emit: impl FnOnce(&mut Body) -> u32) -> u32 {
        if let Some(m) = &self.intern {
            if let Some(e) = m.get(&key) {
                return *e;
            }
        }
        let e = emit(self);
        if let Some(m) = &mut self.intern {
            m.insert(key, e);
        }
        e
    }

    fn term(&mut self, t: &T) -> u32 {
        let key = format!("{t:?}");
        match t.clone() {
            T::Var(w) => self.memo(key, |b| {
                let we = b.wire(w);
                b.ctor(b.term_sort, "TVar", vec![Value::Ref(ElemRef::Local(we))])
            }),
            T::Const(n, d) => self.memo(key, |b| {
                let lit = Literal::q(n, d).expect("canonical q");
                b.ctor(b.term_sort, "TConst", vec![Value::Lit(lit)])
            }),
            T::Neg(x) => {
                let xe = self.term(&x);
                self.memo(key, |b| {
                    b.ctor(b.term_sort, "TNeg", vec![Value::Ref(ElemRef::Local(xe))])
                })
            }
            T::Add(l, r) | T::Sub(l, r) | T::Mul(l, r) => {
                let name = match t {
                    T::Add(..) => "TAdd",
                    T::Sub(..) => "TSub",
                    _ => "TMul",
                };
                let (le, re) = (self.term(&l), self.term(&r));
                self.memo(key, |b| {
                    b.ctor(
                        b.term_sort,
                        name,
                        vec![
                            Value::Ref(ElemRef::Local(le)),
                            Value::Ref(ElemRef::Local(re)),
                        ],
                    )
                })
            }
        }
    }

    fn formula(&mut self, f: &F) -> u32 {
        let key = format!("{f:?}");
        match f.clone() {
            F::Atom(b, l, r) => {
                let name = [
                    "FAtomLT", "FAtomLE", "FAtomEQ", "FAtomGE", "FAtomGT", "FAtomNE",
                ][usize::from(b.min(5))];
                let (le, re) = (self.term(&l), self.term(&r));
                self.memo(key, |bd| {
                    bd.ctor(
                        bd.formula_sort,
                        name,
                        vec![
                            Value::Ref(ElemRef::Local(le)),
                            Value::Ref(ElemRef::Local(re)),
                        ],
                    )
                })
            }
            F::And(l, r) => {
                let (le, re) = (self.formula(&l), self.formula(&r));
                self.memo(key, |b| {
                    b.ctor(
                        b.formula_sort,
                        "FAnd",
                        vec![
                            Value::Ref(ElemRef::Local(le)),
                            Value::Ref(ElemRef::Local(re)),
                        ],
                    )
                })
            }
            F::True => self.memo(key, |b| b.ctor(b.formula_sort, "FTrue", vec![])),
        }
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

/// Evaluate one relation over cells through the provider's full path.
fn ev_cells(rel: &str, args: &[Value], rows: &CertRows) -> Result<bool, String> {
    let p = common::provider();
    let local = p.local_by_name(rel).expect("claimed relation");
    let cells: Vec<Vec<u8>> = args
        .iter()
        .map(|v| {
            let mut buf = Vec::new();
            v.encode(&mut buf);
            buf
        })
        .collect();
    let refs: Vec<&[u8]> = cells.iter().map(|c| c.as_slice()).collect();
    match p.filter_rows(local, &refs, rows) {
        Verdict::Holds => Ok(true),
        Verdict::Fails => Ok(false),
        Verdict::Refused(reason) => Err(reason),
    }
}

/// Evaluate one relation over emitted elements.
fn ev(
    rel: &str,
    bowtie: u64,
    formula: u32,
    l: u32,
    r: u32,
    rows: &CertRows,
) -> Result<bool, String> {
    let args = [
        Value::Lit(Literal::nat(bowtie)),
        Value::Ref(ElemRef::Local(formula)),
        Value::Ref(ElemRef::Local(l)),
        Value::Ref(ElemRef::Local(r)),
    ];
    ev_cells(rel, &args, rows)
}

/// Emit (l, r, φ) and evaluate both relations against the reference.
fn check_both(interned: bool, bowtie: u64, l: &T, r: &T, f: &F) {
    let mut b = Body::new(interned);
    let (le, re, fe) = (b.term(l), b.term(r), b.formula(f));
    let rows = b.rows();
    assert_eq!(
        ev("atomicCompareForm", bowtie, fe, le, re, &rows).expect("decidable"),
        form_ref(bowtie, l, r, f),
        "form: bowtie={bowtie} l={l:?} r={r:?} f={f:?} interned={interned}"
    );
    assert_eq!(
        ev("atomicCompareZero", bowtie, fe, le, re, &rows).expect("decidable"),
        zero_ref(bowtie, l, r, f),
        "zero: bowtie={bowtie} l={l:?} r={r:?} f={f:?} interned={interned}"
    );
}

// ---------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------

fn sample_lr() -> (T, T) {
    (
        T::Add(Box::new(T::Var(0)), Box::new(cq(1, 2))),
        T::Mul(Box::new(T::Var(1)), Box::new(T::Neg(Box::new(cq(3, 1))))),
    )
}

#[test]
fn form_positive_all_bowties_both_interning_modes() {
    let (l, r) = sample_lr();
    for interned in [true, false] {
        for b in 0..5u64 {
            let f = F::Atom(b as u8, l.clone(), r.clone());
            check_both(interned, b, &l, &r, &f);
        }
    }
}

#[test]
fn zero_positive_all_bowties_both_interning_modes() {
    let (l, r) = sample_lr();
    for interned in [true, false] {
        for b in 0..5u64 {
            let f = F::Atom(
                b as u8,
                T::Sub(Box::new(l.clone()), Box::new(r.clone())),
                T::Const(0, 1),
            );
            check_both(interned, b, &l, &r, &f);
        }
    }
}

#[test]
fn decided_negatives() {
    let (l, r) = sample_lr();
    // Wrong operator; swapped arms; out-of-range bowtie (5 = the NE
    // constructor's slot — exists as a formula, unreachable by coding;
    // 7 = nothing at all); non-atomic heads; wrong constant; Add for Sub.
    let cases: Vec<(u64, F)> = vec![
        (3, F::Atom(2, l.clone(), r.clone())),
        (2, F::Atom(2, r.clone(), l.clone())),
        (5, F::Atom(5, l.clone(), r.clone())),
        (7, F::Atom(0, l.clone(), r.clone())),
        (
            1,
            F::And(
                Box::new(F::Atom(1, l.clone(), r.clone())),
                Box::new(F::True),
            ),
        ),
        (0, F::True),
        (
            2,
            F::Atom(
                2,
                T::Sub(Box::new(l.clone()), Box::new(r.clone())),
                T::Const(1, 1),
            ),
        ),
        (
            2,
            F::Atom(
                2,
                T::Add(Box::new(l.clone()), Box::new(r.clone())),
                T::Const(0, 1),
            ),
        ),
        (
            2,
            F::Atom(
                2,
                T::Sub(Box::new(r.clone()), Box::new(l.clone())),
                T::Const(0, 1),
            ),
        ),
    ];
    for interned in [true, false] {
        for (b, f) in &cases {
            check_both(interned, *b, &l, &r, f);
        }
    }
}

/// Structural equality across DISTINCT elements: a non-interned body
/// materializes `l` twice; the atom is built over one copy and asked
/// about the other — true, because "is the atomic formula" is
/// structural (the Lean realization compares decoded inductives;
/// interning is the writer's choice).
#[test]
fn structural_equality_across_duplicate_elements() {
    let (l, r) = sample_lr();
    let mut b = Body::new(false);
    let f = F::Atom(3, l.clone(), r.clone());
    let fe = b.formula(&f);
    // Fresh, structurally-identical copies of l and r.
    let (le2, re2) = (b.term(&l), b.term(&r));
    let rows = b.rows();
    assert_eq!(ev("atomicCompareForm", 3, fe, le2, re2, &rows), Ok(true));
    assert_eq!(ev("atomicCompareForm", 2, fe, le2, re2, &rows), Ok(false));
}

/// Wires are nominal: same structure over DIFFERENT wires is a decided
/// false; different TVar elements over the SAME wire are equal.
#[test]
fn wires_compare_nominally() {
    let mut b = Body::new(false);
    let f = F::Atom(0, T::Var(0), cq(1, 1));
    let fe = b.formula(&f);
    let same_wire = b.term(&T::Var(0));
    let other_wire = b.term(&T::Var(1));
    let one = b.term(&cq(1, 1));
    let rows = b.rows();
    assert_eq!(
        ev("atomicCompareForm", 0, fe, same_wire, one, &rows),
        Ok(true)
    );
    assert_eq!(
        ev("atomicCompareForm", 0, fe, other_wire, one, &rows),
        Ok(false)
    );
}

// ---------------------------------------------------------------------
// Refusals (loud, never guessed)
// ---------------------------------------------------------------------

#[test]
fn bare_element_refuses() {
    let mut b = Body::new(false);
    let bare = b.elta(b.formula_sort);
    let (l, r) = sample_lr();
    let (le, re) = (b.term(&l), b.term(&r));
    let rows = b.rows();
    let err = ev("atomicCompareForm", 0, bare, le, re, &rows).expect_err("undecidable");
    assert!(err.contains("no constructor row"), "wrong arm: {err}");
}

#[test]
fn ambiguous_constructor_refuses() {
    let mut b = Body::new(false);
    let (l, r) = sample_lr();
    let (le, re) = (b.term(&l), b.term(&r));
    // One formula element claimed by TWO constructor rows (P-FUN
    // territory the projection rejects; eval must not pick).
    let f = b.elta(b.formula_sort);
    for name in ["FAtomLT", "FAtomLE"] {
        b.ops.push(Op::Funa {
            fun: b.ext(b.fun[name]),
            args: vec![
                Value::Ref(ElemRef::Local(le)),
                Value::Ref(ElemRef::Local(re)),
            ],
            value: Value::Ref(ElemRef::Local(f)),
        });
    }
    let rows = b.rows();
    let err = ev("atomicCompareForm", 0, f, le, re, &rows).expect_err("ambiguous");
    assert!(err.contains("multiple constructor"), "wrong arm: {err}");
}

#[test]
fn cyclic_rows_refuse_at_depth() {
    let mut b = Body::new(false);
    // Two distinct self-referential terms: e = TNeg(e). P-ACYCLIC
    // rejects such rows at projection; eval must terminate loudly.
    let mk_cycle = |b: &mut Body| {
        let e = b.elta(b.term_sort);
        b.ops.push(Op::Funa {
            fun: b.ext(b.fun["TNeg"]),
            args: vec![Value::Ref(ElemRef::Local(e))],
            value: Value::Ref(ElemRef::Local(e)),
        });
        e
    };
    let (c1, c2) = (mk_cycle(&mut b), mk_cycle(&mut b));
    let one = b.term(&cq(1, 1));
    let f = b.ctor(
        b.formula_sort,
        "FAtomLT",
        vec![
            Value::Ref(ElemRef::Local(c1)),
            Value::Ref(ElemRef::Local(one)),
        ],
    );
    let rows = b.rows();
    let err = ev("atomicCompareForm", 0, f, c2, one, &rows).expect_err("cyclic");
    assert!(err.contains("cyclic"), "wrong arm: {err}");
}

#[test]
fn arity_dtype_and_context_arms_are_loud() {
    let mut b = Body::new(false);
    let (l, r) = sample_lr();
    let f = F::Atom(0, l.clone(), r.clone());
    let (le, re, fe) = (b.term(&l), b.term(&r), b.formula(&f));
    let rows = b.rows();
    // Arity: the family takes 4.
    let two = [Value::Lit(Literal::nat(0)), Value::Ref(ElemRef::Local(fe))];
    let err = ev_cells("atomicCompareForm", &two, &rows).expect_err("arity");
    assert!(err.contains("expects 4 argument"), "wrong arm: {err}");
    // bowtie must be a Nat literal.
    let args = [
        Value::Lit(Literal::q(1, 2).unwrap()),
        Value::Ref(ElemRef::Local(fe)),
        Value::Ref(ElemRef::Local(le)),
        Value::Ref(ElemRef::Local(re)),
    ];
    let err = ev_cells("atomicCompareForm", &args, &rows).expect_err("dtype");
    assert!(err.contains("argument 0 must be a Nat"), "wrong arm: {err}");
    // Element positions must be refs.
    let args = [
        Value::Lit(Literal::nat(0)),
        Value::Lit(Literal::nat(7)),
        Value::Ref(ElemRef::Local(le)),
        Value::Ref(ElemRef::Local(re)),
    ];
    let err = ev_cells("atomicCompareForm", &args, &rows).expect_err("ref");
    assert!(err.contains("argument 1"), "wrong arm: {err}");
    // External refs are out of this leg's single-body context.
    let args = [
        Value::Lit(Literal::nat(0)),
        Value::Ref(ElemRef::External {
            dep_index: 0,
            counter: 3,
        }),
        Value::Ref(ElemRef::Local(le)),
        Value::Ref(ElemRef::Local(re)),
    ];
    let err = ev_cells("atomicCompareForm", &args, &rows).expect_err("external");
    assert!(err.contains("row-context argument 1"), "wrong arm: {err}");
    // An empty row context has no structure in view: loud.
    let empty = CertRows::empty();
    let args = [
        Value::Lit(Literal::nat(0)),
        Value::Ref(ElemRef::Local(fe)),
        Value::Ref(ElemRef::Local(le)),
        Value::Ref(ElemRef::Local(re)),
    ];
    let err = ev_cells("atomicCompareForm", &args, &empty).expect_err("no rows");
    assert!(err.contains("row-context"), "wrong arm: {err}");
}

// ---------------------------------------------------------------------
// Differential proptest
// ---------------------------------------------------------------------

fn arb_term() -> impl Strategy<Value = T> {
    let leaf = prop_oneof![
        (0u32..3).prop_map(T::Var),
        (-3i64..4, 1u64..4).prop_map(|(n, d)| cq(n, d)),
    ];
    leaf.prop_recursive(3, 12, 2, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(l, r)| T::Add(Box::new(l), Box::new(r))),
            (inner.clone(), inner.clone()).prop_map(|(l, r)| T::Sub(Box::new(l), Box::new(r))),
            (inner.clone(), inner.clone()).prop_map(|(l, r)| T::Mul(Box::new(l), Box::new(r))),
            inner.prop_map(|t| T::Neg(Box::new(t))),
        ]
    })
}

/// φ modes: exactly the Form shape, exactly the Zero shape, or an
/// independent draw (mismatch density, with rare accidental hits the
/// reference adjudicates).
fn arb_case() -> impl Strategy<Value = (u64, T, T, F, bool)> {
    (
        0u64..7,
        arb_term(),
        arb_term(),
        prop_oneof![Just(0u8), Just(1u8), Just(2u8),],
        (0u8..6, arb_term(), arb_term()),
        any::<bool>(),
    )
        .prop_map(|(bowtie, l, r, mode, (fb, fl, fr), interned)| {
            let f = match mode {
                0 => F::Atom(u8::try_from(bowtie.min(5)).unwrap(), l.clone(), r.clone()),
                1 => F::Atom(
                    u8::try_from(bowtie.min(5)).unwrap(),
                    T::Sub(Box::new(l.clone()), Box::new(r.clone())),
                    T::Const(0, 1),
                ),
                _ => F::Atom(fb.min(5), fl, fr),
            };
            (bowtie, l, r, f, interned)
        })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(96))]
    /// Oracle verdicts match the AST reference for both relations, both
    /// interning modes, across positive and perturbed shapes.
    #[test]
    fn atomic_compare_matches_ast_reference(
        (bowtie, l, r, f, interned) in arb_case()
    ) {
        check_both(interned, bowtie, &l, &r, &f);
    }
}
