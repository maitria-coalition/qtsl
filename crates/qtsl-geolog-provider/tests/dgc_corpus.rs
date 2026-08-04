//! Committed-corpus conformance for the DtmcContraction finite face:
//! the experiments repo's EV-bracket dev-oracle corpus (the
//! coupon-collector5 and israeli-jalfon4 chains with their canonical
//! certificate claims), transcribed to the pure core's grain and
//! checked to land in the SAME verdict classes as the dev oracle —
//! positives ACCEPT with the exact committed claim values, and every
//! v0 mutant locus lands in its manifest class. The template-magnitude
//! loci (the v0 `M` line's sign/domination mutants) are deliberately
//! absent: the sealed species stores no derived magnitude, so those
//! lies are UNREPRESENTABLE here — the stronger posture — and they
//! remain dev-oracle-lane loci until that lane retires.
//!
//! Chain data source: `probprog/out/ev/{coupon-collector5-u80,
//! israeli-jalfon4-u31}.spec.json`; claim values: the committed
//! `.evc` certificates beside them. Both transcribed verbatim (the
//! spec's `done_0` terminal is simply an unweighted, rowless state
//! at this grain).

use num_bigint::{BigInt, BigUint};
use qtsl_geolog_provider::dgc::{
    check_dgc_ev_bracket, check_dgc_genform, check_dgc_partial_lo, check_dgc_survival_tail,
    check_dgc_z_one, DgcQuery, DgcViolation,
};
use qtsl_geolog_provider::qq::QQ;
use std::str::FromStr;

/// Parse `"num/den"` (arbitrary precision — the corpus L values run
/// past 2^100).
fn qs(s: &str) -> QQ {
    let (n, d) = s.split_once('/').expect("num/den");
    QQ::new(
        BigInt::from_str(n.trim()).expect("numerator"),
        BigUint::from_str(d.trim()).expect("denominator"),
    )
}

fn q(n: i64, d: u64) -> QQ {
    QQ::new(BigInt::from(n), BigUint::from(d))
}

// ---------------------------------------------------------------- cc5

/// coupon-collector5 at horizon 80 — states: 0 done_0, 1..=5 s0..s4.
/// The stored rows are the spec's nine; weights the certificate's
/// left-eigenvector component (min 1/5, κ = 5); rate 4/5.
fn cc5(horizon: usize, c: QQ) -> DgcQuery {
    DgcQuery {
        ns: 6,
        horizon,
        offset: 0,
        c,
        weights: vec![
            (1, q(1, 1)),
            (2, q(4, 5)),
            (3, q(3, 5)),
            (4, q(2, 5)),
            (5, q(1, 5)),
        ],
        rows: vec![
            (1, 2, q(1, 1)),
            (2, 2, q(1, 5)),
            (2, 3, q(4, 5)),
            (3, 3, q(2, 5)),
            (3, 4, q(3, 5)),
            (4, 4, q(3, 5)),
            (4, 5, q(2, 5)),
            (5, 0, q(1, 5)),
            (5, 5, q(4, 5)),
        ],
        init: vec![(1, q(1, 1))],
    }
}

/// The committed cc5-u80 certificate's claim values, verbatim.
const CC5_L: &str = "7554915969017325327206714963037717659085173439094884112/661744490042422139897126953655970282852649688720703125";
const CC5_EV_HI: &str = "37774581306588263966936493018873421011708886851406963536/3308722450212110699485634768279851414263248443603515625";

#[test]
fn cc5_positives_accept_exactly() {
    let dq = cc5(80, q(4, 5));
    assert!(check_dgc_genform(&dq).unwrap().is_ok());
    assert!(check_dgc_partial_lo(&dq, &qs(CC5_L)).unwrap().is_ok());
    assert!(check_dgc_ev_bracket(&dq, &qs(CC5_L), &qs(CC5_EV_HI))
        .unwrap()
        .is_ok());
    // claim tail 5/1 4/5 — the κ-normalized envelope with EQUALITY:
    // W(80) = (4/5)^80 exactly (left eigenvector), so
    // 5·(4/5)^80·(1/5) = W. No unit floor is demanded (min V = 1/5):
    // the conversion is the derived reciprocal, the committed
    // corpus checks verbatim.
    assert!(check_dgc_survival_tail(&dq, &q(5, 1), &q(4, 5))
        .unwrap()
        .is_ok());
    // The relation the v0 cert never claimed still holds on this
    // witness (rows total, init in-region, c < 1, positive minimum) —
    // pinned so the z-one semantics is corpus-anchored too.
    assert!(check_dgc_z_one(&dq).unwrap().is_ok());
}

#[test]
fn cc5_claim_values_are_canonical() {
    // The committed values are the SHARPEST admissible: one grain
    // tighter on each claim flips the verdict.
    let dq = cc5(80, q(4, 5));
    // partial-lo is exactly L: the tiniest increment fails.
    let eps = qs("1/661744490042422139897126953655970282852649688720703125");
    let above = qs(CC5_L).add(&eps);
    assert_eq!(
        check_dgc_partial_lo(&dq, &above).unwrap(),
        Err(DgcViolation::Claim)
    );
    // ev hi is exactly L + κW/(1−c): any decrement fails.
    let hi_below = qs(CC5_EV_HI).sub(&eps);
    assert_eq!(
        check_dgc_ev_bracket(&dq, &qs(CC5_L), &hi_below).unwrap(),
        Err(DgcViolation::Claim)
    );
    // tail coefficient 5 is exact: 4/1 fails at the envelope.
    assert_eq!(
        check_dgc_survival_tail(&dq, &q(4, 1), &q(4, 5)).unwrap(),
        Err(DgcViolation::Claim)
    );
}

#[test]
fn cc5_mutant_loci_land_in_class() {
    // gamma-neg → the rate range refusal (the dev oracle's template
    // sign side-condition survives as the 0 ≤ c demand).
    assert!(check_dgc_genform(&cc5(80, q(-4, 5))).is_err());
    // c-tighter (3/5 with the 4/5 eigenvector weights) → transfer
    // refuted, decided FALSE.
    assert!(matches!(
        check_dgc_genform(&cc5(80, q(3, 5))).unwrap(),
        Err(DgcViolation::Transfer { .. })
    ));
    // partial inflated past the exact sum → FAIL.
    assert_eq!(
        check_dgc_partial_lo(&cc5(80, q(4, 5)), &q(12, 1)).unwrap(),
        Err(DgcViolation::Claim)
    );
    // ev hi tightened to the lower endpoint → FAIL.
    assert_eq!(
        check_dgc_ev_bracket(&cc5(80, q(4, 5)), &qs(CC5_L), &qs(CC5_L)).unwrap(),
        Err(DgcViolation::Claim)
    );
    // w-zero (the s4 weight zeroed): the conversion claims REFUSE —
    // κ has no value (the dev oracle refused the whole certificate;
    // this species refuses exactly the claims that spend the
    // conversion, and the demand/partial tiers stay lemma-faithful).
    let mut wz = cc5(80, q(4, 5));
    wz.weights[4] = (5, q(0, 1));
    assert!(check_dgc_ev_bracket(&wz, &qs(CC5_L), &qs(CC5_EV_HI)).is_err());
    assert!(check_dgc_survival_tail(&wz, &q(5, 1), &q(4, 5)).is_err());
    assert!(check_dgc_z_one(&wz).is_err());
    // widened EV bracket (positive control) → ACCEPT.
    assert!(
        check_dgc_ev_bracket(&cc5(80, q(4, 5)), &qs(CC5_L), &q(12, 1))
            .unwrap()
            .is_ok()
    );
}

// ---------------------------------------------------------------- ij4

/// israeli-jalfon4 at the given horizon — states: 0 done_0, then the
/// eleven alive configurations and the START state in the wire
/// order below. The stored rows are the spec's 48; the weights the
/// eigen-tight per-state certificate (min 1, κ = 1); rate 1/2;
/// anchor offset 1 (the Bernoulli(1/2)^4 prologue is one
/// deterministic transition).
fn ij4(horizon: usize, offset: usize, c: QQ) -> DgcQuery {
    // index: 0 done_0, 1 s3, 2 s5, 3 s6, 4 s7, 5 s9, 6 s10, 7 s11,
    //        8 s12, 9 s13, 10 s14, 11 s15, 12 s16.
    let w = |n: i64, d: u64| q(n, d);
    DgcQuery {
        ns: 13,
        horizon,
        offset,
        c,
        weights: vec![
            (1, w(1, 1)),
            (2, w(1, 1)),
            (3, w(1, 1)),
            (4, w(5, 4)),
            (5, w(1, 1)),
            (6, w(1, 1)),
            (7, w(1, 1)),
            (8, w(1, 1)),
            (9, w(3, 2)),
            (10, w(21, 16)),
            (11, w(21, 16)),
            (12, w(99, 64)),
        ],
        rows: vec![
            // s10
            (6, 0, q(1, 2)),
            (6, 2, q(1, 2)),
            // s11
            (7, 0, q(1, 2)),
            (7, 2, q(1, 2)),
            // s12
            (8, 0, q(1, 2)),
            (8, 1, q(1, 4)),
            (8, 3, q(1, 4)),
            // s13
            (9, 0, q(1, 4)),
            (9, 1, q(3, 8)),
            (9, 3, q(3, 8)),
            // s14
            (10, 0, q(3, 8)),
            (10, 1, q(1, 4)),
            (10, 2, q(1, 8)),
            (10, 3, q(1, 8)),
            (10, 4, q(1, 8)),
            // s15
            (11, 0, q(3, 8)),
            (11, 1, q(1, 4)),
            (11, 2, q(1, 8)),
            (11, 3, q(1, 8)),
            (11, 4, q(1, 8)),
            // s16 (START)
            (12, 0, q(5, 16)),
            (12, 6, q(1, 16)),
            (12, 7, q(1, 16)),
            (12, 8, q(1, 16)),
            (12, 9, q(1, 16)),
            (12, 10, q(1, 16)),
            (12, 11, q(1, 16)),
            (12, 1, q(1, 16)),
            (12, 2, q(1, 16)),
            (12, 3, q(1, 16)),
            (12, 4, q(1, 16)),
            (12, 5, q(1, 16)),
            // s3
            (1, 0, q(1, 2)),
            (1, 8, q(1, 4)),
            (1, 5, q(1, 4)),
            // s5
            (2, 0, q(1, 2)),
            (2, 6, q(1, 2)),
            // s6
            (3, 0, q(1, 2)),
            (3, 1, q(1, 4)),
            (3, 5, q(1, 4)),
            // s7
            (4, 0, q(3, 8)),
            (4, 6, q(1, 8)),
            (4, 7, q(1, 8)),
            (4, 1, q(1, 8)),
            (4, 5, q(1, 4)),
            // s9
            (5, 0, q(1, 2)),
            (5, 1, q(1, 4)),
            (5, 3, q(1, 4)),
        ],
        init: vec![(12, q(1, 1))],
    }
}

/// The committed ij4-u31 certificate's claim values, verbatim.
const IJ4_L31: &str = "100126424989/68719476736";
/// … and u101's partial sum (the context-depth twin).
const IJ4_L101: &str = "118208418471282391689567573901213/81129638414606681695789005144064";

#[test]
fn ij4_positives_accept_exactly() {
    let dq = ij4(31, 1, q(1, 2));
    assert!(check_dgc_genform(&dq).unwrap().is_ok());
    assert!(check_dgc_partial_lo(&dq, &qs(IJ4_L31)).unwrap().is_ok());
    // claim ev [L, 373/256]: the eigen-tight certificate's upper
    // endpoint IS the exact truth of the expected exit time.
    assert!(check_dgc_ev_bracket(&dq, &qs(IJ4_L31), &q(373, 256))
        .unwrap()
        .is_ok());
    // claim tail 99/64 1/2: κ = 1 (unit minimum), W(31) = the
    // eigen decay (99/64)·2⁻³¹ — equality at the envelope.
    assert!(check_dgc_survival_tail(&dq, &q(99, 64), &q(1, 2))
        .unwrap()
        .is_ok());
    assert!(check_dgc_z_one(&dq).unwrap().is_ok());
}

#[test]
fn ij4_u101_positives_accept_exactly() {
    let dq = ij4(101, 1, q(1, 2));
    assert!(check_dgc_partial_lo(&dq, &qs(IJ4_L101)).unwrap().is_ok());
    assert!(check_dgc_ev_bracket(&dq, &qs(IJ4_L101), &q(373, 256))
        .unwrap()
        .is_ok());
    assert!(check_dgc_survival_tail(&dq, &q(99, 64), &q(1, 2))
        .unwrap()
        .is_ok());
}

#[test]
fn ij4_ev_upper_is_tight() {
    // hi one grain under 373/256 fails: the bracket's upper endpoint
    // sits ON the truth.
    let dq = ij4(31, 1, q(1, 2));
    let below = q(373, 256).sub(&qs("1/137438953472"));
    assert_eq!(
        check_dgc_ev_bracket(&dq, &qs(IJ4_L31), &below).unwrap(),
        Err(DgcViolation::Claim)
    );
}

#[test]
fn ij4_offset_loci_land_in_class() {
    // offset-early: k = 2 claims a two-step deterministic prologue,
    // but P[T > 1] = 11/16 — REFUSE at the determinism recompute.
    assert!(check_dgc_partial_lo(&ij4(31, 2, q(1, 2)), &q(0, 1)).is_err());
    assert!(check_dgc_genform(&ij4(31, 2, q(1, 2))).is_err());
    // offset beyond the horizon — REFUSE.
    assert!(check_dgc_partial_lo(&ij4(31, 99, q(1, 2)), &q(0, 1)).is_err());
    // offset-dropped: k = 0 with the k = 1 claims kept — the
    // warranted assembly gains the prologue's survival mass 1, so
    // the kept EV upper endpoint sits below it: decided FALSE at the
    // EV claim (the partial-lo claim alone stays admissible — L only
    // grew — exactly the dev oracle's class split).
    let dropped = ij4(31, 0, q(1, 2));
    assert!(check_dgc_partial_lo(&dropped, &qs(IJ4_L31))
        .unwrap()
        .is_ok());
    assert_eq!(
        check_dgc_ev_bracket(&dropped, &qs(IJ4_L31), &q(373, 256)).unwrap(),
        Err(DgcViolation::Claim)
    );
}

#[test]
fn ij4_mutant_loci_land_in_class() {
    // gamma-neg → rate range refusal.
    assert!(check_dgc_genform(&ij4(31, 1, q(-1, 2))).is_err());
    // c-tighter (1/3 under the eigen-tight 1/2 weights): every
    // transfer row held with EQUALITY at 1/2, so any tightening
    // refutes — decided FALSE.
    assert!(matches!(
        check_dgc_genform(&ij4(31, 1, q(1, 3))).unwrap(),
        Err(DgcViolation::Transfer { .. })
    ));
    // w-zero (the s3 weight zeroed) → conversion refusals.
    let mut wz = ij4(31, 1, q(1, 2));
    wz.weights[0] = (1, q(0, 1));
    assert!(check_dgc_ev_bracket(&wz, &qs(IJ4_L31), &q(373, 256)).is_err());
    assert!(check_dgc_survival_tail(&wz, &q(99, 64), &q(1, 2)).is_err());
    // re-entry (the dev oracle's terminal-rows recompute, this
    // species' regional face): a stored row from done_0 back into
    // the region — REFUSE.
    let mut re = ij4(31, 1, q(1, 2));
    re.rows.push((0, 1, q(1, 1)));
    let e = check_dgc_genform(&re).expect_err("re-entry refuses");
    assert!(e.contains("re-entry"), "{e}");
    // scale-doubled positive control: all weights doubled, claims
    // unchanged — the κ-normalized assembly is scale-invariant.
    let mut sc = ij4(31, 1, q(1, 2));
    for (_, v) in sc.weights.iter_mut() {
        *v = v.mul(&q(2, 1));
    }
    assert!(check_dgc_ev_bracket(&sc, &qs(IJ4_L31), &q(373, 256))
        .unwrap()
        .is_ok());
    assert!(check_dgc_survival_tail(&sc, &q(99, 64), &q(1, 2))
        .unwrap()
        .is_ok());
    // IJ-m1, the floor face, priced honestly: the κ-normalized
    // assembly is scale-invariant in BOTH directions, so the
    // scale-HALVED shape also accepts — the floor's load-bearing
    // tooth is the committed Lean countermodel
    // (`aliveTail_needs_floor` guards the RULE: a non-positive
    // minimum, not a sub-unit one, is what the checker refuses —
    // the conversion-refusal cases above).
    let mut sh = ij4(31, 1, q(1, 2));
    for (_, v) in sh.weights.iter_mut() {
        *v = v.mul(&q(1, 2));
    }
    assert!(check_dgc_survival_tail(&sh, &q(99, 64), &q(1, 2))
        .unwrap()
        .is_ok());
    // widened positive control.
    assert!(
        check_dgc_ev_bracket(&ij4(31, 1, q(1, 2)), &qs(IJ4_L31), &q(12, 1))
            .unwrap()
            .is_ok()
    );
}
