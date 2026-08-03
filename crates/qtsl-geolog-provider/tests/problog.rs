//! The ProbLog family exercised end to end through provider
//! dispatch: the smokers exemplar's two fixtures verify, and the
//! exemplar's eight designed-locus mutants flip provider verdicts at
//! the same loci (same certificates, provider
//! verdicts flip where the tamper was designed).
//!
//! Ground truth was minted by an exemplar pipeline maintained
//! outside this tree (producer + independent checker); the numbers
//! below are transcribed from its receipts; the atom interning is this
//! test's own (atom ids are producer-side vocabulary — the
//! `program_digest` idiom).
//!
//! Atom interning (18 atoms):
//!   0–2   stress(a|b|c)          — coin facts, coins 0–2 at 3/10
//!   3–8   influences(·,·)        — coin facts, coins 3–8 at 1/5
//!           3 = (b,a), 4 = (c,a), 5 = (a,b), 6 = (c,b), 7 = (a,c), 8 = (b,c)
//!   9–14  friend(·,·)            — det facts
//!           9 = (a,b), 10 = (b,a), 11 = (a,c), 12 = (c,a), 13 = (b,c), 14 = (c,b)
//!   15–17 smokes(a|b|c)          — derived; query = 15

mod common;

use common::{ev, qtslcert, QTSLCERT};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;

const OWN: [u8; 32] = [0x53; 32];

struct KitBody {
    ops: Vec<Op>,
    next: u32,
    deps: Vec<[u8; 32]>,
}

impl KitBody {
    fn new() -> KitBody {
        KitBody {
            ops: Vec::new(),
            next: 0,
            deps: vec![QTSLCERT],
        }
    }

    fn xref(&self, c: Chid) -> ElemRef {
        let dep_index = self
            .deps
            .iter()
            .position(|d| *d == c.0)
            .expect("constructor chid homed in a dep") as u32;
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

    fn ctor(&mut self, fun: Chid, args: Vec<Value>) -> u32 {
        let e = self.fresh();
        self.ops.push(Op::Funa {
            fun: self.xref(fun),
            args,
            value: Value::Ref(ElemRef::Local(e)),
        });
        e
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

fn qc_fun(name: &str) -> Chid {
    qtslcert()
        .fun(name)
        .unwrap_or_else(|| panic!("certificate fun `{name}`"))
        .chid
}

fn lref(e: u32) -> Value {
    Value::Ref(ElemRef::Local(e))
}

fn qv(num: i64, den: u64) -> Value {
    Value::Lit(Literal::q(num, den).expect("canonical q"))
}

fn natv(n: u64) -> Value {
    Value::Lit(Literal::nat(n))
}

fn shapev(xs: &[u64]) -> Value {
    Value::Lit(Literal::shape(xs))
}

fn emit_coins(b: &mut KitBody, coins: &[(u64, (i64, u64))]) -> u32 {
    let mut cur = b.ctor(qc_fun("qpcNil"), vec![]);
    for &(id, (n, d)) in coins.iter().rev() {
        cur = b.ctor(qc_fun("qpcCons"), vec![natv(id), qv(n, d), lref(cur)]);
    }
    cur
}

fn emit_facts(b: &mut KitBody, facts: &[(u64, u64)]) -> u32 {
    let mut cur = b.ctor(qc_fun("qpfNil"), vec![]);
    for &(atom, coin) in facts.iter().rev() {
        cur = b.ctor(qc_fun("qpfCons"), vec![natv(atom), natv(coin), lref(cur)]);
    }
    cur
}

fn emit_clauses(b: &mut KitBody, clauses: &[(u64, &[u64])]) -> u32 {
    let mut cur = b.ctor(qc_fun("qpkNil"), vec![]);
    for &(head, body) in clauses.iter().rev() {
        cur = b.ctor(qc_fun("qpkCons"), vec![shapev(body), natv(head), lref(cur)]);
    }
    cur
}

fn emit_setlist(b: &mut KitBody, sets: &[&[u64]]) -> u32 {
    let mut cur = b.ctor(qc_fun("qpsNil"), vec![]);
    for set in sets.iter().rev() {
        cur = b.ctor(qc_fun("qpsCons"), vec![shapev(set), lref(cur)]);
    }
    cur
}

/// Emit a program value: wire field order (clauses, coins, dets,
/// facts, query).
fn emit_prog(
    b: &mut KitBody,
    coins: &[(u64, (i64, u64))],
    dets: &[u64],
    facts: &[(u64, u64)],
    clauses: &[(u64, &[u64])],
    query: u64,
) -> u32 {
    let cl = emit_clauses(b, clauses);
    let co = emit_coins(b, coins);
    let fa = emit_facts(b, facts);
    b.ctor(
        qc_fun("qplogMk"),
        vec![lref(cl), lref(co), shapev(dets), lref(fa), natv(query)],
    )
}

// --------------------------------------------------------------- data

/// Coins: 0–2 stress at 3/10, 3–8 influences at 1/5.
const COINS: &[(u64, (i64, u64))] = &[
    (0, (3, 10)),
    (1, (3, 10)),
    (2, (3, 10)),
    (3, (1, 5)),
    (4, (1, 5)),
    (5, (1, 5)),
    (6, (1, 5)),
    (7, (1, 5)),
    (8, (1, 5)),
];

/// friend(·,·), atoms 9–14 — deterministic.
const DETS: &[u64] = &[9, 10, 11, 12, 13, 14];

/// Coin fact atoms: coin i attaches atom i (stress + influences).
const FACTS: &[(u64, u64)] = &[
    (0, 0),
    (1, 1),
    (2, 2),
    (3, 3),
    (4, 4),
    (5, 5),
    (6, 6),
    (7, 7),
    (8, 8),
];

/// The producer's grounding of smokers.pl (bodies as canonical sets).
const CLAUSES: &[(u64, &[u64])] = &[
    (15, &[0]),         // smokes(a) <- stress(a)
    (16, &[1]),         // smokes(b) <- stress(b)
    (17, &[2]),         // smokes(c) <- stress(c)
    (15, &[3, 9, 16]),  // smokes(a) <- friend(a,b), influences(b,a), smokes(b)
    (15, &[4, 11, 17]), // smokes(a) <- friend(a,c), influences(c,a), smokes(c)
    (16, &[5, 10, 15]), // smokes(b) <- friend(b,a), influences(a,b), smokes(a)
    (16, &[6, 13, 17]), // smokes(b) <- friend(b,c), influences(c,b), smokes(c)
    (17, &[7, 12, 15]), // smokes(c) <- friend(c,a), influences(a,c), smokes(a)
    (17, &[8, 14, 16]), // smokes(c) <- friend(c,b), influences(b,c), smokes(b)
];

const QUERY: u64 = 15; // smokes(a)

/// The minimal-explanation antichain (receipts: `antichain`).
const ANTICHAIN: &[&[u64]] = &[&[0], &[1, 3], &[2, 4], &[1, 4, 8], &[2, 3, 6]];

/// The verified cuts (receipts: `cuts`).
const CUTS: &[&[u64]] = &[&[0, 1, 2], &[0, 3, 4]];

/// exact = 48861/125000; upper = 69/125; fixture-2 lower = 9537/25000.
const EXACT: (i64, u64) = (48861, 125000);
const UPPER: (i64, u64) = (69, 125);
const LOWER2: (i64, u64) = (9537, 25000);

fn smokers(b: &mut KitBody) -> u32 {
    emit_prog(b, COINS, DETS, FACTS, CLAUSES, QUERY)
}

// ----------------------------------------------------- fixture 1 + 2

#[test]
fn fixture1_verifies_through_dispatch() {
    let mut b = KitBody::new();
    let prog = smokers(&mut b);
    let expls = emit_setlist(&mut b, ANTICHAIN);
    let cuts = emit_setlist(&mut b, CUTS);
    let rows = b.rows();

    assert_eq!(ev("qtsl_problog_wf", &[&lref(prog)], &rows), Ok(true));
    // P3: every antichain row derives the query.
    for e in ANTICHAIN {
        assert_eq!(
            ev("qtsl_problog_derives", &[&lref(prog), &shapev(e)], &rows),
            Ok(true),
            "antichain row {e:?} derives"
        );
    }
    // P5: both cuts block.
    for c in CUTS {
        assert_eq!(
            ev("qtsl_problog_blocks", &[&shapev(c), &lref(prog)], &rows),
            Ok(true),
            "cut {c:?} blocks"
        );
    }
    // P2: exact by definitional enumeration (512 worlds).
    assert_eq!(
        ev(
            "qtsl_problog_exact",
            &[&qv(EXACT.0, EXACT.1), &lref(prog)],
            &rows
        ),
        Ok(true)
    );
    // P3+P4: lower over the complete antichain equals exact (a fixture
    // fact — completeness is never an obligation).
    assert_eq!(
        ev(
            "qtsl_problog_lower",
            &[&lref(expls), &qv(EXACT.0, EXACT.1), &lref(prog)],
            &rows
        ),
        Ok(true)
    );
    // P5+P6: upper = min over the two cuts.
    assert_eq!(
        ev(
            "qtsl_problog_upper",
            &[&lref(cuts), &qv(UPPER.0, UPPER.1), &lref(prog)],
            &rows
        ),
        Ok(true)
    );
}

#[test]
fn fixture2_bracket_shape_verifies() {
    // The beyond-enumeration judgment shape: explanation SUBSET lower
    // + cut upper, no exact row. Bracket [0.38148, 0.552] contains
    // fixture 1's exact value (the cross-fixture receipt lives with
    // the exemplar; here the two claims verify independently).
    let mut b = KitBody::new();
    let prog = smokers(&mut b);
    let subset = emit_setlist(&mut b, &[&[0], &[1, 3], &[2, 4]]);
    let cuts = emit_setlist(&mut b, CUTS);
    let rows = b.rows();

    assert_eq!(
        ev(
            "qtsl_problog_lower",
            &[&lref(subset), &qv(LOWER2.0, LOWER2.1), &lref(prog)],
            &rows
        ),
        Ok(true)
    );
    assert_eq!(
        ev(
            "qtsl_problog_upper",
            &[&lref(cuts), &qv(UPPER.0, UPPER.1), &lref(prog)],
            &rows
        ),
        Ok(true)
    );
}

// ------------------------------------------------ the mutant battery
//
// The exemplar's eight designed-locus tampers, reproduced through
// provider dispatch (receipts: `mutant_expected_loci`). Each mutant
// flips the verdict at its designed obligation and nowhere it
// shouldn't.

#[test]
fn m1_coin_tamper_flips_exact() {
    // coins[0].prob 3/10 -> 2/5; the stale exact claim fails P2.
    let mut coins = COINS.to_vec();
    coins[0].1 = (2, 5);
    let mut b = KitBody::new();
    let prog = emit_prog(&mut b, &coins, DETS, FACTS, CLAUSES, QUERY);
    let rows = b.rows();
    assert_eq!(ev("qtsl_problog_wf", &[&lref(prog)], &rows), Ok(true));
    assert_eq!(
        ev(
            "qtsl_problog_exact",
            &[&qv(EXACT.0, EXACT.1), &lref(prog)],
            &rows
        ),
        Ok(false)
    );
}

#[test]
fn m2_clause_drop_flips_exact_and_the_orphaned_explanation() {
    // Drop smokes(a) <- friend(a,b), influences(b,a), smokes(b).
    let clauses: Vec<(u64, &[u64])> = CLAUSES
        .iter()
        .copied()
        .filter(|(h, b)| !(*h == 15 && *b == [3, 9, 16]))
        .collect();
    assert_eq!(clauses.len(), CLAUSES.len() - 1);
    let mut b = KitBody::new();
    let prog = emit_prog(&mut b, COINS, DETS, FACTS, &clauses, QUERY);
    let rows = b.rows();
    // P2 (the receipts' headline locus)…
    assert_eq!(
        ev(
            "qtsl_problog_exact",
            &[&qv(EXACT.0, EXACT.1), &lref(prog)],
            &rows
        ),
        Ok(false)
    );
    // …and the P3 sibling the exemplar notes ("P3 also fires"): the
    // {stress(b), influences(b,a)} explanation loses its clause.
    assert_eq!(
        ev(
            "qtsl_problog_derives",
            &[&lref(prog), &shapev(&[1, 3])],
            &rows
        ),
        Ok(false)
    );
}

#[test]
fn m3_fake_explanation_flips_derives_and_lower() {
    // [3] (influences(b,a) alone) derives nothing.
    let mut b = KitBody::new();
    let prog = smokers(&mut b);
    let mut padded: Vec<&[u64]> = ANTICHAIN.to_vec();
    padded.push(&[3]);
    let expls = emit_setlist(&mut b, &padded);
    let rows = b.rows();
    assert_eq!(
        ev("qtsl_problog_derives", &[&lref(prog), &shapev(&[3])], &rows),
        Ok(false)
    );
    assert_eq!(
        ev(
            "qtsl_problog_lower",
            &[&lref(expls), &qv(EXACT.0, EXACT.1), &lref(prog)],
            &rows
        ),
        Ok(false)
    );
}

#[test]
fn m4_fake_cut_flips_blocks_and_upper() {
    // {influences(b,a), influences(c,a)} misses stress(a): not a cut.
    let mut b = KitBody::new();
    let prog = smokers(&mut b);
    let cuts = emit_setlist(&mut b, &[&[0, 1, 2], &[3, 4]]);
    let rows = b.rows();
    assert_eq!(
        ev(
            "qtsl_problog_blocks",
            &[&shapev(&[3, 4]), &lref(prog)],
            &rows
        ),
        Ok(false)
    );
    assert_eq!(
        ev(
            "qtsl_problog_upper",
            &[&lref(cuts), &qv(UPPER.0, UPPER.1), &lref(prog)],
            &rows
        ),
        Ok(false)
    );
}

#[test]
fn m5_bracket_tamper_flips_lower() {
    // lower nudged up by 1/1000: 48861/125000 + 1/1000 = 24493/62500.
    let mut b = KitBody::new();
    let prog = smokers(&mut b);
    let expls = emit_setlist(&mut b, ANTICHAIN);
    let rows = b.rows();
    assert_eq!(
        ev(
            "qtsl_problog_lower",
            &[&lref(expls), &qv(24493, 62500), &lref(prog)],
            &rows
        ),
        Ok(false)
    );
}

#[test]
fn m6_double_count_is_refused_at_exact() {
    // THE CRUX: the naive free-semiring sum over the minimal antichain
    // claims 111/250 — shared coins double-counted. Refused by
    // re-enumeration, exactly as in the exemplar.
    let mut b = KitBody::new();
    let prog = smokers(&mut b);
    let rows = b.rows();
    assert_eq!(
        ev("qtsl_problog_exact", &[&qv(111, 250), &lref(prog)], &rows),
        Ok(false)
    );
    // The event-level lower over the same rows carries the RIGHT
    // number — the two-sided receipt that the antichain itself was
    // never the problem.
    let expls = emit_setlist(&mut b, ANTICHAIN);
    let rows = b.rows();
    assert_eq!(
        ev(
            "qtsl_problog_lower",
            &[&lref(expls), &qv(111, 250), &lref(prog)],
            &rows
        ),
        Ok(false),
        "the double-counted number is not the inclusion–exclusion value either"
    );
}

#[test]
fn m7_prob_range_flips_wf_and_measure_relations_refuse() {
    // coins[3].prob = 11/10: P1 territory — wf decides false, and the
    // measure-carrying relations refuse rather than evaluate over a
    // malformed measure.
    let mut coins = COINS.to_vec();
    coins[3].1 = (11, 10);
    let mut b = KitBody::new();
    let prog = emit_prog(&mut b, &coins, DETS, FACTS, CLAUSES, QUERY);
    let rows = b.rows();
    assert_eq!(ev("qtsl_problog_wf", &[&lref(prog)], &rows), Ok(false));
    let refused = ev(
        "qtsl_problog_exact",
        &[&qv(EXACT.0, EXACT.1), &lref(prog)],
        &rows,
    );
    assert!(
        refused.is_err(),
        "exact over a malformed measure must refuse, got {refused:?}"
    );
    // The saturation relations read no probabilities and stay decided.
    assert_eq!(
        ev("qtsl_problog_derives", &[&lref(prog), &shapev(&[0])], &rows),
        Ok(true)
    );
}

#[test]
fn m8_fixture2_fake_cut_flips_blocks() {
    // {stress(b), stress(c)} leaves stress(a) live: not a cut.
    let mut b = KitBody::new();
    let prog = smokers(&mut b);
    let rows = b.rows();
    assert_eq!(
        ev(
            "qtsl_problog_blocks",
            &[&shapev(&[1, 2]), &lref(prog)],
            &rows
        ),
        Ok(false)
    );
}

// ---------------------------------------- Bonferroni truncation (r4)
//
// The residue-4 judgment through full dispatch: where the full
// inclusion–exclusion cap refuses (k > 16 rows), the even-depth
// prefix certifies a sound lower bound — Bonferroni's inequality as
// the third soundness fact. The wide exemplar: 18 coins at 1/100,
// query ← any coin, 18 singleton explanation rows. Depth-2 prefix =
// 18/100 − C(18,2)/100² = 1647/10000, a lower bound on the exact
// 1 − (99/100)^18.

/// 18 coins at 1/100 (atoms 0–17 on coins 0–17), one clause
/// `18 ← {i}` per coin; query 18.
fn wide18(b: &mut KitBody) -> u32 {
    let coins: Vec<(u64, (i64, u64))> = (0..18).map(|i| (i, (1, 100))).collect();
    let facts: Vec<(u64, u64)> = (0..18).map(|i| (i, i)).collect();
    let bodies: Vec<[u64; 1]> = (0..18).map(|i| [i]).collect();
    let clauses: Vec<(u64, &[u64])> = bodies.iter().map(|s| (18, s.as_slice())).collect();
    emit_prog(b, &coins, &[], &facts, &clauses, 18)
}

fn wide18_rows() -> Vec<Vec<u64>> {
    (0..18u64).map(|i| vec![i]).collect()
}

#[test]
fn bonferroni_certifies_where_the_full_ie_cap_refuses() {
    let mut b = KitBody::new();
    let prog = wide18(&mut b);
    let sets: Vec<Vec<u64>> = wide18_rows();
    let set_slices: Vec<&[u64]> = sets.iter().map(|s| s.as_slice()).collect();
    let expls = emit_setlist(&mut b, &set_slices);
    let rows = b.rows();
    // The un-truncated relation refuses 18 rows (the designed cap)…
    let refused = ev(
        "qtsl_problog_lower",
        &[&lref(expls), &qv(1647, 10000), &lref(prog)],
        &rows,
    );
    assert!(
        refused.is_err(),
        "full IE over 18 rows must refuse, got {refused:?}"
    );
    // …and the truncation row decides, certifying the sound bound.
    assert_eq!(
        ev(
            "qtsl_problog_bonferroni",
            &[&natv(2), &lref(expls), &qv(1647, 10000), &lref(prog)],
            &rows
        ),
        Ok(true)
    );
}

#[test]
fn m9_odd_depth_truncation_flips() {
    // Depth 1's prefix S1 = 18/100 over-counts the union — an odd
    // depth is decided false even with arithmetic matching its own
    // (unsound) prefix.
    let mut b = KitBody::new();
    let prog = wide18(&mut b);
    let sets = wide18_rows();
    let set_slices: Vec<&[u64]> = sets.iter().map(|s| s.as_slice()).collect();
    let expls = emit_setlist(&mut b, &set_slices);
    let rows = b.rows();
    assert_eq!(
        ev(
            "qtsl_problog_bonferroni",
            &[&natv(1), &lref(expls), &qv(18, 100), &lref(prog)],
            &rows
        ),
        Ok(false)
    );
}

#[test]
fn m10_truncation_overclaim_flips() {
    let mut b = KitBody::new();
    let prog = wide18(&mut b);
    let sets = wide18_rows();
    let set_slices: Vec<&[u64]> = sets.iter().map(|s| s.as_slice()).collect();
    let expls = emit_setlist(&mut b, &set_slices);
    let rows = b.rows();
    // The S1 over-count smuggled in at even depth…
    assert_eq!(
        ev(
            "qtsl_problog_bonferroni",
            &[&natv(2), &lref(expls), &qv(18, 100), &lref(prog)],
            &rows
        ),
        Ok(false)
    );
    // …and a claim above even the full inclusion–exclusion value
    // (2/10 > 1 − (99/100)^18 ≈ 0.1655).
    assert_eq!(
        ev(
            "qtsl_problog_bonferroni",
            &[&natv(2), &lref(expls), &qv(2, 10), &lref(prog)],
            &rows
        ),
        Ok(false)
    );
}

#[test]
fn bonferroni_full_depth_matches_lower_on_the_smokers_antichain() {
    // Differential inside the family: at depth ≥ k (even) the prefix
    // IS the full inclusion–exclusion sum, so the truncation row and
    // the full-IE row certify the same value on fixture 1's antichain.
    let mut b = KitBody::new();
    let prog = smokers(&mut b);
    let expls = emit_setlist(&mut b, ANTICHAIN);
    let rows = b.rows();
    assert_eq!(
        ev(
            "qtsl_problog_bonferroni",
            &[&natv(6), &lref(expls), &qv(EXACT.0, EXACT.1), &lref(prog)],
            &rows
        ),
        Ok(true)
    );
}

#[test]
fn bonferroni_term_budget_refuses_through_dispatch() {
    // 80 singleton rows at depth 4: C(80,4) alone exceeds the 2^20
    // term budget — refusal, never a verdict (the R-CAP posture).
    let mut b = KitBody::new();
    let coins: Vec<(u64, (i64, u64))> = (0..80).map(|i| (i, (1, 100))).collect();
    let facts: Vec<(u64, u64)> = (0..80).map(|i| (i, i)).collect();
    let bodies: Vec<[u64; 1]> = (0..80).map(|i| [i]).collect();
    let clauses: Vec<(u64, &[u64])> = bodies.iter().map(|s| (80, s.as_slice())).collect();
    let prog = emit_prog(&mut b, &coins, &[], &facts, &clauses, 80);
    let sets: Vec<Vec<u64>> = (0..80u64).map(|i| vec![i]).collect();
    let set_slices: Vec<&[u64]> = sets.iter().map(|s| s.as_slice()).collect();
    let expls = emit_setlist(&mut b, &set_slices);
    let rows = b.rows();
    let out = ev(
        "qtsl_problog_bonferroni",
        &[&natv(4), &lref(expls), &qv(1, 2), &lref(prog)],
        &rows,
    );
    assert!(out.is_err(), "term budget must refuse, got {out:?}");
}

// ------------------------------------------- decided content + refusal

#[test]
fn coin_set_arguments_are_decided_content() {
    let mut b = KitBody::new();
    let prog = smokers(&mut b);
    let rows = b.rows();
    // Non-canonical world (not strictly ascending): decided false.
    assert_eq!(
        ev(
            "qtsl_problog_derives",
            &[&lref(prog), &shapev(&[3, 1])],
            &rows
        ),
        Ok(false)
    );
    // Undeclared coin: decided false.
    assert_eq!(
        ev(
            "qtsl_problog_derives",
            &[&lref(prog), &shapev(&[42])],
            &rows
        ),
        Ok(false)
    );
}

#[test]
fn unconstructed_elements_refuse() {
    let mut b = KitBody::new();
    let ghost = b.fresh(); // an element no constructor row produces
    let rows = b.rows();
    let out = ev("qtsl_problog_wf", &[&lref(ghost)], &rows);
    assert!(
        out.is_err(),
        "unconstructed program must refuse, got {out:?}"
    );
}

#[test]
fn foreign_constructor_refuses() {
    // A QBagVal element handed to the program argument: constructed,
    // but by a fun outside the problog kit's rosters — refusal, never
    // a guessed verdict.
    let mut b = KitBody::new();
    let toks = b.ctor(qc_fun("qbtNil"), vec![]);
    let bag = b.ctor(qc_fun("qbagMk"), vec![natv(1), lref(toks)]);
    let rows = b.rows();
    let out = ev("qtsl_problog_wf", &[&lref(bag)], &rows);
    assert!(out.is_err(), "foreign constructor must refuse, got {out:?}");
}

// ------------------------------- msw switch domains ----------------
//
// The die-chain exemplar through provider dispatch: two rolls of a
// loaded three-sided die (switch domains 0 and 1, outcomes at 1/2,
// 1/3, 1/6) plus a free bonus coin at 1/10; atoms 0-6 are the fact
// atoms, 7 = match, 8 = win, 9 = the impossible both-outcomes
// conjunction. Hand values over 3 x 3 x 2 = 18 worlds (checker-battery
// parity: the exemplar's die_msw fixtures): exact P(win) = 9/20, the
// complete antichain's exclusivity-aware inclusion-exclusion equals
// it, cut {0,4,5,6} bounds it by 31/40 under the grouped formula.

/// Coin rows with optional switch domains, emitted via qpcConsD where
/// a domain is present (wire field order: dom, id, prob, tail).
fn emit_coins_msw(b: &mut KitBody, coins: &[(u64, (i64, u64), Option<u64>)]) -> u32 {
    let mut cur = b.ctor(qc_fun("qpcNil"), vec![]);
    for &(id, (n, d), dom) in coins.iter().rev() {
        cur = match dom {
            Some(dm) => b.ctor(
                qc_fun("qpcConsD"),
                vec![natv(dm), natv(id), qv(n, d), lref(cur)],
            ),
            None => b.ctor(qc_fun("qpcCons"), vec![natv(id), qv(n, d), lref(cur)]),
        };
    }
    cur
}

const DIE_COINS: &[(u64, (i64, u64), Option<u64>)] = &[
    (0, (1, 2), Some(0)),
    (1, (1, 3), Some(0)),
    (2, (1, 6), Some(0)),
    (3, (1, 2), Some(1)),
    (4, (1, 3), Some(1)),
    (5, (1, 6), Some(1)),
    (6, (1, 10), None),
];

const DIE_FACTS: &[(u64, u64)] = &[(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

const DIE_CLAUSES: &[(u64, &[u64])] = &[
    (7, &[0, 3]), // match <- roll1(1), roll2(1)
    (7, &[1, 4]),
    (7, &[2, 5]),
    (8, &[7]),    // win <- match
    (8, &[6]),    // win <- bonus
    (9, &[0, 1]), // the impossible conjunction
];

const DIE_ANTICHAIN: &[&[u64]] = &[&[0, 3], &[1, 4], &[2, 5], &[6]];

fn die_prog(b: &mut KitBody, coins: &[(u64, (i64, u64), Option<u64>)], query: u64) -> u32 {
    let cl = emit_clauses(b, DIE_CLAUSES);
    let co = emit_coins_msw(b, coins);
    let fa = emit_facts(b, DIE_FACTS);
    b.ctor(
        qc_fun("qplogMk"),
        vec![lref(cl), lref(co), shapev(&[]), lref(fa), natv(query)],
    )
}

#[test]
fn die_msw_verifies_through_dispatch() {
    let mut b = KitBody::new();
    let prog = die_prog(&mut b, DIE_COINS, 8);
    let expls = emit_setlist(&mut b, DIE_ANTICHAIN);
    let cuts = emit_setlist(&mut b, &[&[0, 4, 5, 6], &[0, 1, 2, 6]]);
    let rows = b.rows();

    assert_eq!(ev("qtsl_problog_wf", &[&lref(prog)], &rows), Ok(true));
    for e in DIE_ANTICHAIN {
        assert_eq!(
            ev("qtsl_problog_derives", &[&lref(prog), &shapev(e)], &rows),
            Ok(true),
            "antichain row {e:?} derives"
        );
    }
    assert_eq!(
        ev(
            "qtsl_problog_blocks",
            &[&shapev(&[0, 4, 5, 6]), &lref(prog)],
            &rows
        ),
        Ok(true)
    );
    // P2: mixed-radix enumeration, 18 worlds, exact 9/20.
    assert_eq!(
        ev("qtsl_problog_exact", &[&qv(9, 20), &lref(prog)], &rows),
        Ok(true)
    );
    // P3+P4: exclusive rows add with no overlap term — the complete
    // antichain's IE equals exact.
    assert_eq!(
        ev(
            "qtsl_problog_lower",
            &[&lref(expls), &qv(9, 20), &lref(prog)],
            &rows
        ),
        Ok(true)
    );
    // P5+P6: grouped miss product; the whole-switch cut contributes
    // the vacuous-but-sound bound 1, min picks 31/40.
    assert_eq!(
        ev(
            "qtsl_problog_upper",
            &[&lref(cuts), &qv(31, 40), &lref(prog)],
            &rows
        ),
        Ok(true)
    );
    // P3+P4-truncated: depth 2 equals the full sum here (all strata
    // past 2 vanish under exclusivity).
    assert_eq!(
        ev(
            "qtsl_problog_bonferroni",
            &[&natv(2), &lref(expls), &qv(9, 20), &lref(prog)],
            &rows
        ),
        Ok(true)
    );
}

#[test]
fn m11_domain_sum_flips_wf_and_measure_relations_refuse() {
    // Roll #1's outcomes re-weighted to 1/2 + 1/4 + 1/6 = 11/12: the
    // exactly-one-of-k measure condition fails — wf decides false,
    // measure relations refuse.
    let mut coins = DIE_COINS.to_vec();
    coins[1].1 = (1, 4);
    let mut b = KitBody::new();
    let prog = die_prog(&mut b, &coins, 8);
    let rows = b.rows();
    assert_eq!(ev("qtsl_problog_wf", &[&lref(prog)], &rows), Ok(false));
    let refused = ev("qtsl_problog_exact", &[&qv(9, 20), &lref(prog)], &rows);
    assert!(
        refused.is_err(),
        "exact over a malformed switch measure must refuse, got {refused:?}"
    );
}

#[test]
fn m12_switch_clash_rows_are_decided_false() {
    let mut b = KitBody::new();
    let prog = die_prog(&mut b, DIE_COINS, 8);
    let clash = emit_setlist(&mut b, &[&[0, 1]]);
    let rows = b.rows();
    // A world naming two outcomes of one switch describes no possible
    // world: decided false at derives, and at the row inside lower.
    assert_eq!(
        ev(
            "qtsl_problog_derives",
            &[&lref(prog), &shapev(&[0, 1])],
            &rows
        ),
        Ok(false)
    );
    assert_eq!(
        ev(
            "qtsl_problog_lower",
            &[&lref(clash), &qv(0, 1), &lref(prog)],
            &rows
        ),
        Ok(false)
    );
}

#[test]
fn m13_independence_ie_is_refused_at_lower() {
    // THE residue-5 boundary: the independence-assuming arithmetic
    // over the same rows gives 5/12 (nonzero overlap terms between
    // exclusive rows); the exclusivity-aware truth is 9/20.
    let mut b = KitBody::new();
    let prog = die_prog(&mut b, DIE_COINS, 8);
    let expls = emit_setlist(&mut b, DIE_ANTICHAIN);
    let rows = b.rows();
    assert_eq!(
        ev(
            "qtsl_problog_lower",
            &[&lref(expls), &qv(5, 12), &lref(prog)],
            &rows
        ),
        Ok(false)
    );
}

#[test]
fn m14_independent_upper_is_refused() {
    // Cut {0,4,5,6}: independent formula 1 - prod(1-p) = 3/4; the
    // grouped truth is 31/40.
    let mut b = KitBody::new();
    let prog = die_prog(&mut b, DIE_COINS, 8);
    let cuts = emit_setlist(&mut b, &[&[0, 4, 5, 6]]);
    let rows = b.rows();
    assert_eq!(
        ev(
            "qtsl_problog_upper",
            &[&lref(cuts), &qv(3, 4), &lref(prog)],
            &rows
        ),
        Ok(false)
    );
    assert_eq!(
        ev(
            "qtsl_problog_upper",
            &[&lref(cuts), &qv(31, 40), &lref(prog)],
            &rows
        ),
        Ok(true)
    );
}

#[test]
fn m15_impossible_conjunction_enumerates_to_zero() {
    // Query 9 needs two outcomes of switch 0 at once: unrepresentable
    // in the msw world space — exact 0 verifies, the independent-
    // Bernoulli mass 1/6 is refused at P2.
    let mut b = KitBody::new();
    let prog = die_prog(&mut b, DIE_COINS, 9);
    let rows = b.rows();
    assert_eq!(
        ev("qtsl_problog_exact", &[&qv(0, 1), &lref(prog)], &rows),
        Ok(true)
    );
    assert_eq!(
        ev("qtsl_problog_exact", &[&qv(1, 6), &lref(prog)], &rows),
        Ok(false)
    );
}

// ----------------- the compiled decision term through dispatch ------
// (`qtsl_problog_compiled` — the exact-beyond-enumeration judgment;
// the deep semantics batteries live beside the core check in
// src/problog.rs, so these cases pin the decode + dispatch plumbing:
// wire field orders, structural sharing, cycle refusal, and the
// arm-list walk.)

fn dec_node(b: &mut KitBody, coin: u64, hi: u32, lo: u32) -> u32 {
    // Wire field order (bytewise): coin, hi, lo.
    b.ctor(qc_fun("qpdDecide"), vec![natv(coin), lref(hi), lref(lo)])
}

fn acc_node(b: &mut KitBody, expl: &[u64]) -> u32 {
    b.ctor(qc_fun("qpdAccept"), vec![shapev(expl)])
}

fn rej_node(b: &mut KitBody, cut: &[u64]) -> u32 {
    b.ctor(qc_fun("qpdReject"), vec![shapev(cut)])
}

fn switch_node(b: &mut KitBody, dom: u64, arms: &[(u64, u32)]) -> u32 {
    let mut cur = b.ctor(qc_fun("qpaNil"), vec![]);
    for &(coin, child) in arms.iter().rev() {
        // Wire field order (bytewise): child, coin, tail.
        cur = b.ctor(qc_fun("qpaCons"), vec![lref(child), natv(coin), lref(cur)]);
    }
    // Wire field order (bytewise): arms, dom.
    b.ctor(qc_fun("qpdSwitch"), vec![lref(cur), natv(dom)])
}

/// The two-coin bracket program (query 3 via coin 0 + det 2, or coin
/// 1): P(query) = 2/3.
fn two_coin(b: &mut KitBody) -> u32 {
    emit_prog(
        b,
        &[(0, (1, 2)), (1, (1, 3))],
        &[2],
        &[(0, 0), (1, 1)],
        &[(3, &[0, 2]), (3, &[1])],
        3,
    )
}

#[test]
fn compiled_verifies_through_dispatch() {
    let mut b = KitBody::new();
    let prog = two_coin(&mut b);
    let a0 = acc_node(&mut b, &[0]);
    let a1 = acc_node(&mut b, &[1]);
    let r01 = rej_node(&mut b, &[0, 1]);
    let d1 = dec_node(&mut b, 1, a1, r01);
    let root = dec_node(&mut b, 0, a0, d1);
    let rows = b.rows();
    // Args in wire field order: p, prog, tree.
    assert_eq!(
        ev(
            "qtsl_problog_compiled",
            &[&qv(2, 3), &lref(prog), &lref(root)],
            &rows
        ),
        Ok(true)
    );
    // A tampered value is decided false at the fold (P10).
    assert_eq!(
        ev(
            "qtsl_problog_compiled",
            &[&qv(1, 2), &lref(prog), &lref(root)],
            &rows
        ),
        Ok(false)
    );
}

#[test]
fn compiled_shares_elements_and_switches_through_dispatch() {
    // One switch (outcomes 0-2 at 1/2, 1/3, 1/6), query = outcome 0's
    // atom: P = 1/2. The two reject arms cite ONE shared element —
    // the row stratum's benign-share class, green through dispatch
    // (the file format's no-share rejection has no image here).
    fn one_switch(b: &mut KitBody) -> u32 {
        let cl = emit_clauses(b, &[]);
        let co = emit_coins_msw(
            b,
            &[
                (0, (1, 2), Some(0)),
                (1, (1, 3), Some(0)),
                (2, (1, 6), Some(0)),
            ],
        );
        let fa = emit_facts(b, &[(0, 0), (1, 1), (2, 2)]);
        b.ctor(
            qc_fun("qplogMk"),
            vec![lref(cl), lref(co), shapev(&[]), lref(fa), natv(0)],
        )
    }
    let mut b = KitBody::new();
    let prog = one_switch(&mut b);
    let a0 = acc_node(&mut b, &[0]);
    let shared_rej = rej_node(&mut b, &[0]);
    let root = switch_node(&mut b, 0, &[(0, a0), (1, shared_rej), (2, shared_rej)]);
    let rows = b.rows();
    assert_eq!(
        ev(
            "qtsl_problog_compiled",
            &[&qv(1, 2), &lref(prog), &lref(root)],
            &rows
        ),
        Ok(true)
    );
    // An arm gap is decided false (structure, P8's image).
    let mut b = KitBody::new();
    let prog = one_switch(&mut b);
    let a0 = acc_node(&mut b, &[0]);
    let r0 = rej_node(&mut b, &[0]);
    let root = switch_node(&mut b, 0, &[(0, a0), (1, r0)]);
    let rows = b.rows();
    assert_eq!(
        ev(
            "qtsl_problog_compiled",
            &[&qv(1, 2), &lref(prog), &lref(root)],
            &rows
        ),
        Ok(false)
    );
}

#[test]
fn compiled_decode_refuses_cycles_and_foreign_elements() {
    // A Decide whose hi edge cites its own element: the decode's
    // ancestor-path cycle refusal (P-ACYCLIC), never a verdict.
    let mut b = KitBody::new();
    let prog = two_coin(&mut b);
    let a0 = acc_node(&mut b, &[0]);
    let e = b.fresh();
    b.ops.push(Op::Funa {
        fun: b.xref(qc_fun("qpdDecide")),
        args: vec![natv(0), lref(e), lref(a0)],
        value: Value::Ref(ElemRef::Local(e)),
    });
    let rows = b.rows();
    assert!(ev(
        "qtsl_problog_compiled",
        &[&qv(1, 1), &lref(prog), &lref(e)],
        &rows
    )
    .is_err());
    // A tree argument citing a non-tree element (the program root)
    // refuses — structure undecidable, not a verdict.
    let mut b = KitBody::new();
    let prog = two_coin(&mut b);
    let rows = b.rows();
    assert!(ev(
        "qtsl_problog_compiled",
        &[&qv(1, 1), &lref(prog), &lref(prog)],
        &rows
    )
    .is_err());
}
