//! The batch-CSR kernel — the lane-conformance proptest battery.
//!
//! Property: for arbitrary batches (accept-shaped, mutant-perturbed,
//! and capacity-refusal-forcing), every [`Lowering`] of
//! [`verify_batch`] agrees instance-for-instance with the `blbatch`
//! reference (`verify_instance`), and the machine-word lanes' verdicts
//! survive their own deferrals (DATERWI: capacity refusal routes to
//! the exact path, never to a guess). The generators deliberately
//! cross three magnitude tiers — comfortable machine words, values
//! near the `i64`/`u64` boundary, and `\sim 2^{100}`-scale bignums —
//! so both the fast paths and the deferral paths are exercised in the
//! same run.

use num_bigint::{BigInt, BigUint};
use proptest::collection::{btree_set, vec};
use proptest::prelude::*;
use qtsl_geolog_provider::blbatch::{verify_instance, ComboAttempt, ComboBranch, ComboExtract};
use qtsl_geolog_provider::blcsr::{verify_batch, CsrBatch, ALL_LOWERINGS};
use qtsl_geolog_provider::qq::QQ;

/// A rational at a chosen magnitude tier. `shift` pushes numerators
/// (and half the time denominators) past any machine width.
fn arb_qq(max_mag: i64, max_den: u64, shift: u32) -> BoxedStrategy<QQ> {
    (
        -max_mag..=max_mag,
        1..=max_den,
        0..=shift,
        proptest::bool::ANY,
    )
        .prop_map(|(n, d, s, shift_den)| {
            let num = BigInt::from(n) << s;
            let den = if shift_den && s > 0 {
                BigUint::from(d) << (s / 2)
            } else {
                BigUint::from(d)
            };
            QQ::new(num, den)
        })
        .boxed()
}

/// Sparse vector over `n_monos` columns: strictly ascending cols,
/// nonzero coefficients (zero draws are dropped — canonical form).
fn arb_sparse(n_monos: u32, val: BoxedStrategy<QQ>) -> BoxedStrategy<Vec<(u32, QQ)>> {
    btree_set(0..n_monos, 0..=(n_monos.min(5) as usize))
        .prop_flat_map(move |cols| {
            let n = cols.len();
            let cols: Vec<u32> = cols.into_iter().collect();
            vec(val.clone(), n).prop_map(move |vals| {
                cols.iter()
                    .copied()
                    .zip(vals)
                    .filter(|(_, q)| !q.is_zero())
                    .collect()
            })
        })
        .boxed()
}

/// One attempt, built accept-shaped (candidates contain every vehicle;
/// conclusion = the exact fold) and then perturbed by the mutation
/// selector: 0 = intact, 1 = λ-sign flip, 2 = conclusion perturbed,
/// 3 = candidate support broken.
fn arb_attempt(tier: u8) -> impl Strategy<Value = ComboAttempt> {
    let (mag, den, shift) = match tier {
        0 => (1_000, 1_000, 0),
        1 => (i64::MAX / 4, u64::MAX / 4, 0),
        _ => (1_000, 1_000, 100),
    };
    (2u32..10, 0usize..4)
        .prop_flat_map(move |(n_monos, n_entries)| {
            let lam = arb_qq(mag, den, shift).prop_map(|q| q.abs()).boxed();
            let veh = arb_sparse(n_monos, arb_qq(mag, den, shift));
            (
                Just(n_monos),
                vec(lam, n_entries),
                vec(veh.clone(), n_entries),
                vec(veh, 0..3),
                0u8..4,
                0..(n_entries.max(1)),
            )
        })
        .prop_map(
            move |(n_monos, lambdas, vehicles, decoys, mutation, victim)| {
                // Exact fold — the accept-shaped conclusion.
                let mut fold = vec![QQ::zero(); n_monos as usize];
                for (l, v) in lambdas.iter().zip(&vehicles) {
                    for (col, c) in v {
                        fold[*col as usize] = fold[*col as usize].add(&l.mul(c));
                    }
                }
                let conclusion: Vec<(u32, QQ)> = fold
                    .into_iter()
                    .enumerate()
                    .filter(|(_, q)| !q.is_zero())
                    .map(|(c, q)| (c as u32, q))
                    .collect();
                let mut cand_polys = vehicles.clone();
                cand_polys.extend(decoys);
                let mut a = ComboAttempt {
                    branch: ComboBranch::Core,
                    n_monos,
                    lambdas,
                    vehicles,
                    cand_polys,
                    conclusion,
                };
                match mutation {
                    1 if !a.lambdas.is_empty()
                        && !a.lambdas[victim % a.lambdas.len()].is_zero() =>
                    {
                        let i = victim % a.lambdas.len();
                        a.lambdas[i] = a.lambdas[i].neg();
                    }
                    2 => {
                        if let Some(first) = a.conclusion.first_mut() {
                            first.1 = first.1.add(&QQ::one());
                        } else {
                            a.conclusion.push((0, QQ::one()));
                        }
                    }
                    3 if !a.vehicles.is_empty() => {
                        let i = victim % a.vehicles.len();
                        // Perturb the vehicle only: membership breaks
                        // unless the perturbed vector still matches a
                        // candidate (agreement is the property either
                        // way — the reference adjudicates).
                        if let Some(first) = a.vehicles[i].first_mut() {
                            first.1 = first.1.add(&QQ::one());
                            if first.1.is_zero() {
                                first.1 = QQ::one();
                            }
                        } else {
                            a.vehicles[i].push((0, QQ::one()));
                        }
                    }
                    _ => {}
                }
                a
            },
        )
}

fn arb_extract(tier: u8) -> impl Strategy<Value = ComboExtract> {
    vec(arb_attempt(tier), 0..3).prop_map(|attempts| ComboExtract {
        decided_false: attempts.is_empty(),
        attempts,
    })
}

/// Batches mix tiers within one run: index 0 = small, 1 = boundary,
/// 2 = bignum (deferral-forcing).
fn arb_batch() -> impl Strategy<Value = Vec<ComboExtract>> {
    vec(
        prop_oneof![arb_extract(0), arb_extract(1), arb_extract(2)],
        0..6,
    )
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Every lowering agrees with the `blbatch` reference on every
    /// instance, across magnitude tiers (deferral included).
    #[test]
    fn lanes_agree_with_reference(extracts in arb_batch()) {
        let want: Vec<bool> = extracts.iter().map(verify_instance).collect();
        let b = CsrBatch::pack(&extracts);
        prop_assert_eq!(b.instances(), extracts.len());
        for lane in ALL_LOWERINGS {
            let out = verify_batch(&b, lane);
            prop_assert_eq!(&out.verdicts, &want, "lane {:?}", lane);
            // Conservation: every attempt is adjudicated exactly once.
            prop_assert_eq!(
                out.attempts_fast + out.attempts_deferred,
                b.attempts(),
                "lane {:?} attempt conservation", lane
            );
        }
    }

    /// Bignum tier forces the machine-word lanes to defer — and the
    /// deferrals stay verdict-exact (the DATERWI property observed,
    /// not assumed).
    #[test]
    fn bignum_tier_defers_exactly(extracts in vec(arb_extract(2), 1..4)) {
        let want: Vec<bool> = extracts.iter().map(verify_instance).collect();
        let b = CsrBatch::pack(&extracts);
        for lane in [qtsl_geolog_provider::blcsr::Lowering::LqqSmall, qtsl_geolog_provider::blcsr::Lowering::LintSmall] {
            let out = verify_batch(&b, lane);
            prop_assert_eq!(&out.verdicts, &want, "lane {:?}", lane);
        }
    }

    /// The move-based flatten ([`CsrBatch::from_extracts`], the feed
    /// twin built on [`CsrBuilder`]) produces PLANE-IDENTICAL batches
    /// to the clone-based `pack` spec — slot for slot, including the
    /// capacity annotations (`small_ok`, `lint_den`).
    #[test]
    fn builder_flatten_equals_pack(extracts in arb_batch()) {
        let packed = CsrBatch::pack(&extracts);
        let moved = CsrBatch::from_extracts(extracts);
        prop_assert_eq!(packed, moved);
    }

    /// Sharded feeding composes: packing split halves and appending
    /// equals packing the whole (the parallel-feed law).
    #[test]
    fn append_of_splits_equals_pack_of_whole(extracts in arb_batch(), split in 0usize..7) {
        let k = split.min(extracts.len());
        let mut left = CsrBatch::pack(&extracts[..k]);
        let right = CsrBatch::pack(&extracts[k..]);
        left.append(right);
        prop_assert_eq!(left, CsrBatch::pack(&extracts));
    }
}
