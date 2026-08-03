//! Verdict-identity battery: the rns lanes (kernels reference always;
//! CUDA when a device is reachable) against the provider's own
//! lowerings and the `blbatch` reference, on the same generator
//! family the provider's blcsr battery uses — three magnitude tiers,
//! accept-shaped constructions, verdict mutants, and the malformed /
//! negative-λ / membership-failure gate cases.

use num_bigint::{BigInt, BigUint};
use num_traits::One;
use proptest::collection::{btree_set, vec as pvec};
use proptest::prelude::*;
use qtsl_geolog_provider::blbatch::{verify_instance, ComboAttempt, ComboBranch, ComboExtract};
use qtsl_geolog_provider::blcsr::{verify_batch, CsrBatch, Lowering};
use qtsl_geolog_provider::qq::QQ;
use qtsl_geolog_provider_gpu::{
    pack, pack_membership, pack_reference, verify_batch_rns, verify_batch_rns_full,
};

// ---- generators (the provider battery's family, transcribed) ----

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

fn arb_sparse(n_monos: u32, val: BoxedStrategy<QQ>) -> BoxedStrategy<Vec<(u32, QQ)>> {
    btree_set(0..n_monos, 0..=(n_monos.min(5) as usize))
        .prop_flat_map(move |cols| {
            let cols: Vec<u32> = cols.into_iter().collect();
            let n = cols.len();
            pvec(val.clone(), n).prop_map(move |vals| {
                cols.iter()
                    .cloned()
                    .zip(vals)
                    .filter(|(_, q)| !q.is_zero())
                    .collect()
            })
        })
        .boxed()
}

fn arb_attempt(shift: u32) -> BoxedStrategy<ComboAttempt> {
    (2u32..9, 1usize..5)
        .prop_flat_map(move |(n_monos, n_entries)| {
            let val = arb_qq(50, 30, shift);
            (
                Just(n_monos),
                pvec(arb_qq(20, 10, shift / 2), n_entries),
                pvec(arb_sparse(n_monos, val.clone()), n_entries),
                pvec(arb_sparse(n_monos, val.clone()), 0..4),
                arb_sparse(n_monos, val),
            )
        })
        .prop_map(|(n_monos, lambdas, vehicles, extra_cands, conclusion)| {
            // candidate pool ⊇ vehicles (so membership can pass), plus noise
            let mut cand_polys = vehicles.clone();
            cand_polys.extend(extra_cands);
            ComboAttempt {
                branch: ComboBranch::Core,
                n_monos,
                lambdas,
                vehicles,
                cand_polys,
                conclusion,
            }
        })
        .boxed()
}

/// Accept-shaped: conclusion = the exact fold; λs forced nonnegative.
fn make_accept(mut a: ComboAttempt) -> ComboAttempt {
    for l in &mut a.lambdas {
        if !l.is_nonneg() {
            *l = l.neg();
        }
    }
    let mut fold: Vec<QQ> = vec![QQ::zero(); a.n_monos as usize];
    for (lam, veh) in a.lambdas.iter().zip(&a.vehicles) {
        for (c, v) in veh {
            fold[*c as usize] = fold[*c as usize].add(&lam.mul(v));
        }
    }
    a.conclusion = fold
        .into_iter()
        .enumerate()
        .filter(|(_, q)| !q.is_zero())
        .map(|(c, q)| (c as u32, q))
        .collect();
    a
}

fn check_all_lanes(extracts: &[ComboExtract]) {
    let want: Vec<bool> = extracts.iter().map(verify_instance).collect();
    let b = CsrBatch::pack(extracts);
    // the columnar feed vs the reference packer: plane-for-plane
    // structural equality (the strongest conformance the descriptor's
    // derived PartialEq affords), on every generated case — gate
    // cases, mutants, and edges included.
    let rns = pack(&b);
    assert_eq!(
        rns,
        pack_reference(&b),
        "columnar pack diverged from the reference packer"
    );
    rns.validate().expect("packed descriptor must validate");
    // provider's own exact lane as the anchor
    assert_eq!(
        verify_batch(&b, Lowering::CsrRef).verdicts,
        want,
        "provider CsrRef lane disagrees with the blbatch reference"
    );
    // the rns reference lane (this crate + kernels, CPU)
    let out = verify_batch_rns(&b);
    assert_eq!(out.verdicts, want, "rns reference lane diverged");
    // the FULL reference path (fold + membership both on kernels
    // reference lanes; host residual = malformed + packed λ̂ signs)
    let out_full = verify_batch_rns_full(&b);
    assert_eq!(out_full.verdicts, want, "full rns reference path diverged");
    assert_eq!(
        out_full.attempts_deferred, out.attempts_deferred,
        "full path must defer exactly the fold-refused attempts"
    );
    // parallel packers must splice to byte-identical descriptors
    #[cfg(feature = "parallel")]
    {
        assert_eq!(
            qtsl_geolog_provider_gpu::pack_par(&b),
            pack(&b),
            "pack_par diverged from pack"
        );
        assert_eq!(
            qtsl_geolog_provider_gpu::pack_membership_par(&b),
            pack_membership(&b),
            "pack_membership_par diverged from pack_membership"
        );
    }
    #[cfg(not(feature = "parallel"))]
    {
        // keep the imports used in every configuration
        let _ = (pack(&b), pack_membership(&b));
    }
    // the CUDA lane, when a device is reachable
    #[cfg(feature = "cuda")]
    {
        use std::sync::OnceLock;
        static GPU: OnceLock<Option<qtsl_geolog_provider_gpu::gpu::GpuBatchVerifier>> =
            OnceLock::new();
        let gpu =
            GPU.get_or_init(
                || match qtsl_geolog_provider_gpu::gpu::GpuBatchVerifier::new() {
                    Ok(g) => Some(g),
                    Err(e) => {
                        eprintln!("SKIP CUDA lane (no usable device): {e}");
                        None
                    }
                },
            );
        if let Some(g) = gpu {
            let gout = g.verify_batch(&b).expect("gpu verify");
            assert_eq!(gout.verdicts, want, "CUDA lane diverged");
            let gfull = g.verify_batch_full(&b).expect("gpu full verify");
            assert_eq!(gfull.verdicts, want, "CUDA full path diverged");
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]

    /// Arbitrary (mostly rejecting) extracts across magnitude tiers.
    #[test]
    fn lanes_agree_arbitrary(
        atts in pvec(arb_attempt(0), 1..4),
        tier in prop_oneof![Just(0u32), Just(70u32), Just(600u32)],
    ) {
        // tier > 0 regenerates values by shifting numerators upward
        let extracts: Vec<ComboExtract> = atts
            .into_iter()
            .map(|mut a| {
                if tier > 0 {
                    for v in a.vehicles.iter_mut().chain(a.cand_polys.iter_mut()) {
                        for (_, q) in v.iter_mut() {
                            *q = QQ::new(q.num() << tier, q.den().clone());
                        }
                    }
                    for (_, q) in a.conclusion.iter_mut() {
                        *q = QQ::new(q.num() << tier, q.den().clone());
                    }
                }
                ComboExtract { decided_false: false, attempts: vec![a] }
            })
            .collect();
        check_all_lanes(&extracts);
    }

    /// Accept-shaped extracts (verdict true) and their mutants
    /// (λ-sign flip, coefficient perturbation, conclusion drop) —
    /// every lane must track every flip.
    #[test]
    fn lanes_agree_accepts_and_mutants(
        base in arb_attempt(40),
        which in any::<prop::sample::Index>(),
        mode in 0u8..3,
    ) {
        let good = make_accept(base);
        let e = ComboExtract { decided_false: false, attempts: vec![good.clone()] };
        prop_assume!(verify_instance(&e)); // sanity: constructed accept
        check_all_lanes(std::slice::from_ref(&e));

        let mut mutant = good;
        match mode {
            0 => {
                // λ-sign flip (first nonzero λ)
                if let Some(l) = mutant.lambdas.iter_mut().find(|l| !l.is_zero()) {
                    *l = l.neg();
                } else {
                    return Ok(());
                }
            }
            1 => {
                // vehicle coefficient perturbation (breaks membership
                // AND the fold)
                let all: usize = mutant.vehicles.iter().map(|v| v.len()).sum();
                if all == 0 { return Ok(()); }
                let mut idx = which.index(all);
                'outer: for v in &mut mutant.vehicles {
                    for (_, q) in v.iter_mut() {
                        if idx == 0 {
                            *q = q.add(&QQ::one());
                            if q.is_zero() { *q = QQ::one(); }
                            break 'outer;
                        }
                        idx -= 1;
                    }
                }
            }
            _ => {
                // conclusion perturbation
                if mutant.conclusion.is_empty() {
                    mutant.conclusion.push((0, QQ::one()));
                } else {
                    let i = which.index(mutant.conclusion.len());
                    mutant.conclusion[i].1 = mutant.conclusion[i].1.add(&QQ::one());
                    if mutant.conclusion[i].1.is_zero() {
                        mutant.conclusion.remove(i);
                    }
                }
            }
        }
        let em = ComboExtract { decided_false: false, attempts: vec![mutant] };
        check_all_lanes(std::slice::from_ref(&em));
    }
}

#[test]
fn gate_cases_and_edges() {
    // the provider blcsr unit fixtures, replayed through the rns lanes
    let q = |n: i64| QQ::from_int(n);
    let qd = |n: i64, d: u64| QQ::new(BigInt::from(n), BigUint::from(d));
    let attempt = ComboAttempt {
        branch: ComboBranch::Core,
        n_monos: 2,
        lambdas: vec![qd(1, 2), q(2)],
        vehicles: vec![vec![(0, q(2)), (1, qd(1, 3))], vec![(0, qd(1, 4))]],
        cand_polys: vec![
            vec![(0, q(2)), (1, qd(1, 3))],
            vec![(0, qd(1, 4))],
            vec![(1, q(7))],
        ],
        conclusion: vec![(0, qd(3, 2)), (1, qd(1, 6))],
    };
    let mut bad_lambda = attempt.clone();
    bad_lambda.lambdas[0] = qd(-1, 2);
    let mut bad_concl = attempt.clone();
    bad_concl.conclusion[0].1 = q(4);
    let mut bad_member = attempt.clone();
    bad_member.vehicles[1][0].1 = qd(1, 5);
    let mut malformed = attempt.clone();
    malformed.lambdas.pop();
    let big = QQ::new(BigInt::from(1) << 700, BigUint::from(3u32));
    let big_attempt = ComboAttempt {
        branch: ComboBranch::Core,
        n_monos: 1,
        lambdas: vec![q(3)],
        vehicles: vec![vec![(0, big.clone())]],
        cand_polys: vec![vec![(0, big)]],
        conclusion: vec![(0, QQ::new(BigInt::from(1) << 700, BigUint::one()))],
    };
    let ex = |a: ComboAttempt| ComboExtract {
        decided_false: false,
        attempts: vec![a],
    };
    let extracts = vec![
        ex(attempt),
        ex(bad_lambda),
        ex(bad_concl),
        ex(bad_member),
        ex(malformed),
        ex(big_attempt),
        ComboExtract {
            decided_false: true,
            attempts: vec![],
        },
    ];
    let want: Vec<bool> = extracts.iter().map(verify_instance).collect();
    assert_eq!(want, [true, false, false, false, false, true, false]);
    check_all_lanes(&extracts);
}

/// The parallel pack path (batches past `PACK_PAR_MIN_NNZ` take the
/// rayon route through both passes) against the reference packer,
/// plane for plane, plus verdict identity — the proptest cases above
/// are all below the threshold, so this pins the other branch.
#[test]
fn parallel_pack_matches_reference_above_threshold() {
    use qtsl_geolog_provider_gpu::PACK_PAR_MIN_NNZ;
    let qd = |n: i64, d: u64| QQ::new(BigInt::from(n), BigUint::from(d));
    let dens = [2u64, 3, 7];
    let (t, m) = (24usize, 40u32);
    let mut extracts = Vec::new();
    let mut nnz = 0usize;
    let mut inst = 0i64;
    while nnz <= PACK_PAR_MIN_NNZ {
        inst += 1;
        // accept-shaped: conclusion computed as the exact fold.
        let lambdas: Vec<QQ> = (0..t)
            .map(|e| qd(1 + (e as i64 % 5), dens[e % 3]))
            .collect();
        let vehicles: Vec<Vec<(u32, QQ)>> = (0..t)
            .map(|e| {
                (0..m)
                    .filter(|c| !(c + e as u32).is_multiple_of(11))
                    .map(|c| {
                        (
                            c,
                            qd(inst + e as i64 + c as i64 + 1, dens[(e + c as usize) % 3]),
                        )
                    })
                    .collect()
            })
            .collect();
        nnz += vehicles.iter().map(|v| v.len()).sum::<usize>();
        let mut fold = vec![QQ::from_int(0); m as usize];
        for (lam, veh) in lambdas.iter().zip(&vehicles) {
            for (c, v) in veh {
                fold[*c as usize] = fold[*c as usize].add(&lam.mul(v));
            }
        }
        let conclusion: Vec<(u32, QQ)> = fold
            .into_iter()
            .enumerate()
            .filter(|(_, v)| !v.is_zero())
            .map(|(c, v)| (c as u32, v))
            .collect();
        extracts.push(ComboExtract {
            decided_false: false,
            attempts: vec![ComboAttempt {
                branch: ComboBranch::Core,
                n_monos: m,
                lambdas,
                vehicles: vehicles.clone(),
                cand_polys: vehicles,
                conclusion,
            }],
        });
    }
    let b = CsrBatch::pack(&extracts);
    assert!(
        b.nnz_col.len() >= PACK_PAR_MIN_NNZ,
        "constructed batch must clear the parallel threshold"
    );
    let rns = pack(&b);
    assert_eq!(
        rns,
        pack_reference(&b),
        "parallel columnar pack diverged from the reference packer"
    );
    rns.validate().expect("packed descriptor must validate");
    let out = verify_batch_rns(&b);
    let want: Vec<bool> = extracts.iter().map(verify_instance).collect();
    assert!(want.iter().all(|&v| v), "accept-shaped batch must accept");
    assert_eq!(
        out.verdicts, want,
        "rns lane diverged on the parallel-pack batch"
    );
}
