//! constfold conformance battery: the flat batch surface's verdicts
//! are pinned, row for row, to the landed per-row `constExactEvalTrue`
//! dispatch through `filter_rows` — the two renderings (columnar
//! planes vs closed term tree) of one shared certificate, compared on
//! synthetic systems rich in FALSE rows (bit-identity on failures is
//! the half that matters for a checker). The lane law throughout: a
//! lane may change cost, never verdicts — so the battery also asserts
//! path-policy neutrality (column vs scatter) and production/reference
//! lane identity, and drives designed-locus mutants through BOTH
//! representations.

mod common;

use common::{ev, stack, STACK};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use num_bigint::{BigInt, BigUint};
use proptest::prelude::*;
use qtsl_geolog_provider::constfold::{
    row_verdict, verify_batch, verify_batch_big, verify_batch_with, ConstFoldBatch, ConstSystem,
    PathPolicy, NONE,
};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use std::collections::BTreeMap;

const OWN: [u8; 32] = [0xC7; 32];

/// Closed-term emitter over the shared synthetic stack —
/// `TConst`/`TAdd`/`TSub`/`TMul` constructor rows with `BigInt`
/// constants (the family's terms are integers; `q_big(c, 1)`).
struct Emit {
    ops: Vec<Op>,
    deps: Vec<[u8; 32]>,
    term_sort: Chid,
    tconst: Chid,
    tadd: Chid,
    tsub: Chid,
    tmul: Chid,
}

impl Emit {
    fn new() -> Emit {
        let s = stack();
        Emit {
            ops: Vec::new(),
            deps: vec![STACK],
            term_sort: s.sort("Term").expect("Term"),
            tconst: s.fun("TConst").expect("TConst").chid,
            tadd: s.fun("TAdd").expect("TAdd").chid,
            tsub: s.fun("TSub").expect("TSub").chid,
            tmul: s.fun("TMul").expect("TMul").chid,
        }
    }

    fn ext(&self, chid: Chid) -> ElemRef {
        let dep_index = self
            .deps
            .iter()
            .position(|h| *h == chid.0)
            .expect("chid homed") as u32;
        ElemRef::External {
            dep_index,
            counter: chid.1,
        }
    }

    fn lref(e: u32) -> Value {
        Value::Ref(ElemRef::Local(e))
    }

    fn ctor(&mut self, fun: Chid, args: Vec<Value>) -> u32 {
        let e = self.ops.len() as u32;
        let sort = self.ext(self.term_sort);
        self.ops.push(Op::Elta { sort });
        let fun = self.ext(fun);
        self.ops.push(Op::Funa {
            fun,
            args,
            value: Self::lref(e),
        });
        e
    }

    fn cint(&mut self, n: &BigInt) -> u32 {
        let lit = Literal::q_big(n.clone(), BigUint::from(1u8)).expect("canonical q");
        self.ctor(self.tconst, vec![Value::Lit(lit)])
    }

    fn add(&mut self, l: u32, r: u32) -> u32 {
        self.ctor(self.tadd, vec![Self::lref(l), Self::lref(r)])
    }
    fn sub(&mut self, l: u32, r: u32) -> u32 {
        self.ctor(self.tsub, vec![Self::lref(l), Self::lref(r)])
    }
    fn mul(&mut self, l: u32, r: u32) -> u32 {
        self.ctor(self.tmul, vec![Self::lref(l), Self::lref(r)])
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

/// Dispatch `constExactEvalTrue {bowtie: Eq, l, r}` through
/// `filter_rows` — the landed per-row path. `Refused` is a battery
/// bug, never a verdict.
fn dispatch_eq(l: u32, r: u32, rows: &CertRows) -> bool {
    let bt = Value::Lit(Literal::nat(2));
    ev(
        "constExactEvalTrue",
        &[&bt, &Emit::lref(l), &Emit::lref(r)],
        rows,
    )
    .expect("dispatch verdict, never a refusal")
}

/// Render ONE conservation column as the certificate's term tree
/// (the `conservation_lhs` grammar: places ascending over the
/// column's accumulated (post, pre), `Mul(y_p, Sub(post, pre))`,
/// right-nested sum, empty sum = Const 0) and dispatch it against 0.
fn landed_conservation(em: &mut Emit, sys: &ConstSystem, y: &[BigInt], col: u32) -> (u32, u32) {
    let mut per: BTreeMap<u32, (BigInt, BigInt)> = BTreeMap::new();
    for i in sys.col_ptr[col as usize] as usize..sys.col_ptr[col as usize + 1] as usize {
        let e = per
            .entry(sys.leaf_place[i])
            .or_insert((BigInt::ZERO, BigInt::ZERO));
        let w = sys.leaf_w[i];
        if w >= 0 {
            e.0 += w;
        } else {
            e.1 += -w;
        }
    }
    let mut terms: Vec<u32> = Vec::new();
    for (p, (post, pre)) in per {
        let yp = em.cint(&y[p as usize]);
        let po = em.cint(&post);
        let pr = em.cint(&pre);
        let d = em.sub(po, pr);
        terms.push(em.mul(yp, d));
    }
    let lhs = terms
        .into_iter()
        .rev()
        .reduce(|acc, t| em.add(t, acc))
        .unwrap_or_else(|| em.cint(&BigInt::ZERO));
    let rhs = em.cint(&BigInt::ZERO);
    (lhs, rhs)
}

/// The charge row's term tree: `Σ_{y_p ≠ 0} Mul(y_p, m0_p)` vs `b`.
fn landed_charge(em: &mut Emit, sys: &ConstSystem, y: &[BigInt], b: &BigInt) -> (u32, u32) {
    let mut terms: Vec<u32> = Vec::new();
    for (p, yp) in y.iter().enumerate() {
        if *yp != BigInt::ZERO {
            let ye = em.cint(yp);
            let me = em.cint(&BigInt::from(sys.m0[p]));
            terms.push(em.mul(ye, me));
        }
    }
    let lhs = terms
        .into_iter()
        .rev()
        .reduce(|acc, t| em.add(t, acc))
        .unwrap_or_else(|| em.cint(&BigInt::ZERO));
    let rhs = em.cint(b);
    (lhs, rhs)
}

/// Row-for-row bit-identity of one attempt against the landed
/// dispatch, plus internal consistency (attempt verdict = AND of row
/// verdicts, first_bad = least failing row).
fn assert_attempt_conformance(batch: &ConstFoldBatch, a: u32, y: &[BigInt], b: &BigInt) {
    let sys = &batch.systems[batch.attempt_sys[a as usize] as usize];
    let mut all = true;
    let mut first_bad = NONE;
    for col in 0..=sys.n_cols {
        let mut em = Emit::new();
        let (l, r) = if col == sys.n_cols {
            landed_charge(&mut em, sys, y, b)
        } else {
            landed_conservation(&mut em, sys, y, col)
        };
        let landed = dispatch_eq(l, r, &em.rows());
        let flat = row_verdict(batch, a, col);
        assert_eq!(flat, landed, "row {col}: flat vs landed dispatch");
        if !flat && first_bad == NONE {
            first_bad = col;
        }
        all &= flat;
    }
    for policy in [
        PathPolicy::Auto,
        PathPolicy::ColumnOnly,
        PathPolicy::ScatterOnly,
    ] {
        let out = verify_batch_with(batch, policy);
        assert_eq!(
            out.ok[a as usize], all,
            "{policy:?}: attempt verdict = AND rows"
        );
        assert_eq!(
            out.first_bad[a as usize], first_bad,
            "{policy:?}: first_bad"
        );
    }
    let big = verify_batch_big(batch);
    assert_eq!(big.ok[a as usize], all, "reference lane verdict");
    assert_eq!(big.first_bad[a as usize], first_bad, "reference first_bad");
}

// ---------------------------------------------------------------------
// generators
// ---------------------------------------------------------------------

#[derive(Debug, Clone)]
struct GenSys {
    n_places: u32,
    n_cols: u32,
    leaves: Vec<(u32, u32, i64)>,
    m0: Vec<i64>,
    /// A vector orthogonal to every column by construction.
    y_true: Vec<BigInt>,
}

/// Systems whose columns are 2-place combinations `w_i = s·y_j`,
/// `w_j = −s·y_i` — exactly orthogonal to `y_true`; plus noise leaves
/// on places where `y_true` is zero (they perturb nothing).
fn gen_sys() -> impl Strategy<Value = GenSys> {
    (2u32..8, 1u32..10, proptest::collection::vec(-4i64..5, 2..8))
        .prop_flat_map(|(np, nc, yvals)| {
            let np = np.max(yvals.len() as u32).min(8);
            let y: Vec<i64> = (0..np as usize)
                .map(|p| yvals.get(p).copied().unwrap_or(0))
                .collect();
            let col = (0u32..np, 0u32..np, 1i64..3);
            (
                Just((np, y)),
                proptest::collection::vec(col, nc as usize),
                proptest::collection::vec(0i64..4, np as usize),
            )
        })
        .prop_map(|((np, y), cols, m0)| {
            let mut leaves = Vec::new();
            let nc = cols.len() as u32;
            for (t, (i, j, s)) in cols.into_iter().enumerate() {
                let (i, j) = (i % np, (j % np));
                if i != j {
                    let wi = s * y[j as usize];
                    let wj = -s * y[i as usize];
                    if wi != 0 {
                        leaves.push((t as u32, i, wi));
                    }
                    if wj != 0 {
                        leaves.push((t as u32, j, wj));
                    }
                }
                // Noise on a zero-coefficient place: contributes 0.
                if let Some(zp) = y.iter().position(|&v| v == 0) {
                    leaves.push((t as u32, zp as u32, s + 1));
                }
            }
            GenSys {
                n_places: np,
                n_cols: nc,
                leaves,
                m0,
                y_true: y.iter().map(|&v| BigInt::from(v)).collect(),
            }
        })
}

fn charge(y: &[BigInt], m0: &[i64]) -> BigInt {
    y.iter().zip(m0).map(|(yp, &m)| yp * BigInt::from(m)).sum()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]

    /// True-by-construction attempts, their mutants, and fully random
    /// attempts: every row bit-identical to the landed dispatch, every
    /// lane and path in agreement.
    #[test]
    fn conformance_vs_landed_dispatch(
        g in gen_sys(),
        yrand in proptest::collection::vec(-3i64..4, 8),
        db in -2i64..3,
    ) {
        let sys = ConstSystem::from_leaves(g.n_places, g.n_cols, &g.leaves, g.m0.clone());
        let mut batch = ConstFoldBatch::new(vec![sys]);
        // Attempt 0: the true invariant with its true charge.
        let b0 = charge(&g.y_true, &g.m0);
        batch.push_attempt(0, &g.y_true, &b0);
        // Attempt 1: same vector, perturbed charge (false iff db != 0).
        batch.push_attempt(0, &g.y_true, &(&b0 + BigInt::from(db)));
        // Attempt 2: a random vector with honestly computed charge
        // (conservation rows usually false — the FALSE-rich stratum).
        let yr: Vec<BigInt> = (0..g.n_places as usize)
            .map(|p| BigInt::from(yrand[p % yrand.len()]))
            .collect();
        let br = charge(&yr, &g.m0);
        batch.push_attempt(0, &yr, &br);

        let out = verify_batch(&batch);
        prop_assert!(out.ok[0], "constructed invariant verifies");
        prop_assert_eq!(out.ok[1], db == 0, "charge perturbation detected");

        let bs: [&BigInt; 3] = [&b0, &(&b0 + BigInt::from(db)), &br];
        let ys: [&[BigInt]; 3] = [&g.y_true, &g.y_true, &yr];
        for a in 0..3u32 {
            assert_attempt_conformance(&batch, a, ys[a as usize], bs[a as usize]);
        }
    }
}

// ---------------------------------------------------------------------
// designed-locus mutants (deterministic)
// ---------------------------------------------------------------------

/// t0: p0 −1, p1 +1; t1: p1 −1, p2 +1; m0 = [3, 1, 0];
/// y = (1,1,1), b = 4.
fn chain() -> (ConstSystem, Vec<BigInt>, BigInt) {
    let sys = ConstSystem::from_leaves(
        3,
        2,
        &[(0, 0, -1), (0, 1, 1), (1, 1, -1), (1, 2, 1)],
        vec![3, 1, 0],
    );
    let y = vec![BigInt::from(1), BigInt::from(1), BigInt::from(1)];
    let b = BigInt::from(4);
    (sys, y, b)
}

#[test]
fn mutant_locus_y_coefficient() {
    let (sys, y, _) = chain();
    let mut ym = y.clone();
    ym[0] += 1;
    let bm = charge(&ym, &sys.m0);
    let mut batch = ConstFoldBatch::new(vec![sys]);
    batch.push_attempt(0, &ym, &bm);
    let out = verify_batch(&batch);
    assert!(!out.ok[0] && out.first_bad[0] == 0, "t0 catches y0+1");
    assert_attempt_conformance(&batch, 0, &ym, &bm);
}

#[test]
fn mutant_locus_leaf_weight() {
    let (_, y, b) = chain();
    // Perturb one plane weight: t1's p2 leaf becomes +2.
    let sys = ConstSystem::from_leaves(
        3,
        2,
        &[(0, 0, -1), (0, 1, 1), (1, 1, -1), (1, 2, 2)],
        vec![3, 1, 0],
    );
    let mut batch = ConstFoldBatch::new(vec![sys]);
    batch.push_attempt(0, &y, &b);
    let out = verify_batch(&batch);
    assert!(
        !out.ok[0] && out.first_bad[0] == 1,
        "t1 catches the leaf fault"
    );
    assert_attempt_conformance(&batch, 0, &y, &b);
}

#[test]
fn mutant_locus_charge_rhs() {
    let (sys, y, b) = chain();
    let n_cols = sys.n_cols;
    let mut batch = ConstFoldBatch::new(vec![sys]);
    let bbad = &b + 1;
    batch.push_attempt(0, &y, &bbad);
    let out = verify_batch(&batch);
    assert!(
        !out.ok[0] && out.first_bad[0] == n_cols,
        "charge row localizes"
    );
    assert_attempt_conformance(&batch, 0, &y, &bbad);
}

#[test]
fn mutant_locus_m0_stale_b() {
    let (_, y, b) = chain();
    // m0 perturbed, b left stale: only the charge row flips.
    let sys = ConstSystem::from_leaves(
        3,
        2,
        &[(0, 0, -1), (0, 1, 1), (1, 1, -1), (1, 2, 1)],
        vec![3, 2, 0],
    );
    let n_cols = sys.n_cols;
    let mut batch = ConstFoldBatch::new(vec![sys]);
    batch.push_attempt(0, &y, &b);
    let out = verify_batch(&batch);
    assert!(!out.ok[0] && out.first_bad[0] == n_cols);
    assert_attempt_conformance(&batch, 0, &y, &b);
}

#[test]
fn mutant_locus_transposition() {
    let (sys, _y, _) = chain();
    // Swap y entries across places with different incidence rows:
    // y = (1,1,1) is symmetric, so use (1,2,3) — a NON-invariant —
    // against its transposed sibling to check both fail identically
    // to dispatch (bit-identity on false verdicts).
    let ya = vec![BigInt::from(1), BigInt::from(2), BigInt::from(3)];
    let yb = vec![BigInt::from(3), BigInt::from(2), BigInt::from(1)];
    let (ba, bb) = (charge(&ya, &sys.m0), charge(&yb, &sys.m0));
    let mut batch = ConstFoldBatch::new(vec![sys]);
    batch.push_attempt(0, &ya, &ba);
    batch.push_attempt(0, &yb, &bb);
    let out = verify_batch(&batch);
    assert!(!out.ok[0] && !out.ok[1]);
    assert_attempt_conformance(&batch, 0, &ya, &ba);
    assert_attempt_conformance(&batch, 1, &yb, &bb);
}

#[test]
fn refused_attempt_conforms_through_exact_lane() {
    // 2^126-scaled invariant: admission refuses, the exact lane
    // carries the verdict, and the landed dispatch (BigInt terms all
    // the way) agrees row for row — including on the scaled MUTANT.
    let (sys, y, b) = chain();
    let big: BigInt = BigInt::from(1u8) << 126;
    let ys: Vec<BigInt> = y.iter().map(|e| e * &big).collect();
    let bs = &b * &big;
    let mut ym = ys.clone();
    ym[0] += &big;
    let bm = charge(&ym, &sys.m0);
    let mut batch = ConstFoldBatch::new(vec![sys]);
    batch.push_attempt(0, &ys, &bs);
    batch.push_attempt(0, &ym, &bm);
    let out = verify_batch(&batch);
    assert!(out.used_big[0] && out.used_big[1], "admission refused both");
    assert!(out.ok[0], "scaled invariant true through the exact lane");
    assert!(!out.ok[1], "scaled mutant still flips");
    assert_attempt_conformance(&batch, 0, &ys, &bs);
    assert_attempt_conformance(&batch, 1, &ym, &bm);
}
