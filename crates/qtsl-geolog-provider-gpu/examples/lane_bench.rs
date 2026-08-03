//! Lane bench: CPU exact lanes vs the rns lanes (CPU channels + CUDA)
//! on synthetic combination batches spanning the measured shape
//! family — fixture-class, promise-class, and the X1-syzygy class
//! (the regime the corpus receipts project as GPU-worthy). Prints a
//! receipts-ready table: shape, lane, wall, µs/instance. The
//! conformance stance rides along: every lane's verdicts are checked
//! for equality on every timed shape before its row prints.
//!
//! Run (device lane): `cargo run --release --features cuda --example
//! lane_bench` — shapes trimmed by `QUICK=1` for smoke.

use num_bigint::{BigInt, BigUint};
use num_traits::One;
use qtsl_geolog_provider::blbatch::{ComboAttempt, ComboBranch, ComboExtract};
use qtsl_geolog_provider::blcsr::attempt_gates_exact;
use qtsl_geolog_provider::blcsr::{verify_batch, CsrBatch, Lowering};
use qtsl_geolog_provider::qq::QQ;
use qtsl_geolog_provider_gpu::{
    pack, pack_membership, pack_reference, verify_batch_rns, verify_batch_rns_full,
};
use std::time::Instant;

/// xorshift — deterministic, dependency-free.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn bits(&mut self, bits: u64) -> BigUint {
        let limbs = (bits as usize).div_ceil(64);
        let mut v: BigUint = BigUint::from(0u32);
        for _ in 0..limbs {
            v = (v << 64) + BigUint::from(self.next());
        }
        (v | BigUint::one()) % (BigUint::one() << bits)
    }
}

/// One accept-shaped attempt at the given shape, built the
/// integer-first way (conclusion accumulated in BigInt at scale D²,
/// divided down once — never per-op rational reduction).
///
/// Denominator structure mirrors real certificates (the X3 audit: a
/// tiny dictionary, 98.2% repeats, lcm barely above any one member):
/// dict entries share one `den_bits`-bit base times a small cofactor,
/// so the per-attempt common denominator D stays ~`den_bits` — the
/// regime the corpus receipts' k=10 tier describes. (An earlier draw
/// of pairwise-random large dens made D their product, blew the
/// channel plan's bound past the prime table, and correctly deferred
/// every attempt to the CPU exact path — the typed-refusal plumbing
/// validated itself; the receipts note carries the story.)
fn synth_attempt(
    rng: &mut Rng,
    entries: usize,
    monos: u32,
    bits: u64,
    den_bits: u64,
    dict: usize,
) -> ComboAttempt {
    const SMALLS: [u32; 4] = [1, 2, 3, 5];
    let base = rng.bits(den_bits) | BigUint::one();
    let dens: Vec<BigUint> = (0..dict)
        .map(|j| &base * BigUint::from(SMALLS[j % SMALLS.len()]))
        .collect();
    let mut d_big = BigUint::one();
    for d in &dens {
        let g = {
            let (mut a, mut b) = (d_big.clone(), d.clone());
            while !num_traits::Zero::is_zero(&b) {
                let r = &a % &b;
                a = b;
                b = r;
            }
            a
        };
        d_big = (&d_big / g) * d;
    }
    // λ_e >= 0 with den from the dict
    let lambdas: Vec<QQ> = (0..entries)
        .map(|e| QQ::new(BigInt::from(rng.next() >> 32), dens[e % dict].clone()))
        .collect();
    // vehicles: dense-ish rows (every column, minus a few holes)
    let vehicles: Vec<Vec<(u32, QQ)>> = (0..entries)
        .map(|e| {
            (0..monos)
                .filter(|c| !(c + e as u32).is_multiple_of(37)) // ~97% density
                .map(|c| {
                    let num = BigInt::from(rng.bits(bits));
                    let num = if rng.next() & 1 == 0 { -num } else { num };
                    (c, QQ::new(num, dens[(e + c as usize) % dict].clone()))
                })
                .collect()
        })
        .collect();
    // conclusion = exact fold, integer-accumulated at scale D²
    let mut acc = vec![BigInt::from(0); monos as usize];
    for (lam, veh) in lambdas.iter().zip(&vehicles) {
        let lam_s = lam.num() * BigInt::from(&d_big / lam.den());
        for (c, q) in veh {
            let v_s = q.num() * BigInt::from(&d_big / q.den());
            acc[*c as usize] += &lam_s * v_s;
        }
    }
    let d2 = &d_big * &d_big;
    let conclusion: Vec<(u32, QQ)> = acc
        .into_iter()
        .enumerate()
        .filter(|(_, v)| !num_traits::Zero::is_zero(v))
        .map(|(c, v)| (c as u32, QQ::new(v, d2.clone())))
        .collect();
    // candidate pool: the vehicles + two noise rows (membership honest,
    // not the axis under measurement)
    let mut cand_polys = vehicles.clone();
    for _ in 0..2 {
        cand_polys.push(vec![(
            0,
            QQ::new(BigInt::from(rng.bits(bits)), dens[0].clone()),
        )]);
    }
    ComboAttempt {
        branch: ComboBranch::Core,
        n_monos: monos,
        lambdas,
        vehicles,
        cand_polys,
        conclusion,
    }
}

fn synth_batch(
    seed: u64,
    n: usize,
    entries: usize,
    monos: u32,
    bits: u64,
    den_bits: u64,
    dict: usize,
) -> CsrBatch {
    let mut rng = Rng(seed | 1);
    let extracts: Vec<ComboExtract> = (0..n)
        .map(|_| ComboExtract {
            decided_false: false,
            attempts: vec![synth_attempt(
                &mut rng, entries, monos, bits, den_bits, dict,
            )],
        })
        .collect();
    CsrBatch::pack(&extracts)
}

fn time<F: FnMut() -> R, R>(mut f: F) -> (R, f64) {
    let t = Instant::now();
    let r = f();
    (r, t.elapsed().as_secs_f64())
}

fn main() {
    let quick = std::env::var("QUICK").is_ok();
    // (name, n, entries, monos, bits, dict)
    let mut shapes: Vec<(&str, usize, usize, u32, u64, u64, usize)> = vec![
        (
            "fixture-class   (T=2,  M=8,   30b/25b)",
            64,
            2,
            8,
            30,
            25,
            2,
        ),
        (
            "promise-class   (T=2,  M=70,  1100b/100b)",
            32,
            2,
            70,
            1100,
            100,
            4,
        ),
        (
            "x1-mini         (T=24, M=40,  600b/600b)",
            32,
            24,
            40,
            600,
            600,
            4,
        ),
        (
            "x1-syzygy-class (T=238,M=400, 600b/600b)",
            8,
            238,
            400,
            600,
            600,
            4,
        ),
    ];
    if !quick {
        shapes.push((
            "x1-syzygy-batch (T=238,M=400, 600b/600b)",
            64,
            238,
            400,
            600,
            600,
            4,
        ));
        // crossover sweep in T at the 600-bit tier
        for t in [4usize, 8, 16, 32, 64, 128] {
            shapes.push(("t-sweep        (M=64, 600b/600b)", 16, t, 64, 600, 600, 4));
        }
    }

    #[cfg(feature = "cuda")]
    let gpu = match qtsl_geolog_provider_gpu::gpu::GpuBatchVerifier::new() {
        Ok(g) => {
            println!("device: {}", g.device_summary().unwrap_or_default());
            Some(g)
        }
        Err(e) => {
            println!("no CUDA device ({e}); CPU lanes only");
            None
        }
    };

    #[allow(unused_mut)]
    let mut scaling_batches: Vec<(String, CsrBatch)> = Vec::new();
    let mut split_rows: Vec<(&str, usize, usize, [f64; 11])> = Vec::new();
    println!(
        "{:<40} {:>4} {:>5} | {:>12} {:>12} {:>12} {:>12} {:>12} {:>10}",
        "shape", "n", "T", "LqqBig", "LintBig", "rns-cpu", "gpu-e2e", "gpu-fold", "channels"
    );
    for (name, n, entries, monos, bits, den_bits, dict) in shapes {
        let b = synth_batch(
            0x5EED_0000 + entries as u64,
            n,
            entries,
            monos,
            bits,
            den_bits,
            dict,
        );
        let inst = b.instances() as f64;

        // conformance anchor for this shape. LqqBig is quadratic in
        // fold length; at the widest batched shape it stops being an
        // instrument and becomes the wall — anchor on LintBig there.
        let skip_lqq = entries >= 200 && n >= 32;
        let (want, t_lint) = time(|| verify_batch(&b, Lowering::LintBig).verdicts);
        assert!(want.iter().all(|&v| v), "accept-shaped batch must accept");
        let t_lqq = if skip_lqq {
            f64::NAN
        } else {
            let (v1, t) = time(|| verify_batch(&b, Lowering::LqqBig).verdicts);
            assert_eq!(want, v1, "LqqBig disagrees");
            t
        };
        let (out_rns, t_rns) = time(|| verify_batch_rns(&b));
        assert_eq!(want, out_rns.verdicts, "rns-cpu disagrees");

        #[allow(unused_mut)] // mutated only under the cuda feature
        let mut gpu_cols = (f64::NAN, f64::NAN, 0usize);
        #[cfg(feature = "cuda")]
        if let Some(g) = &gpu {
            let (out_gpu, t_gpu) = time(|| g.verify_batch(&b).expect("gpu verify"));
            assert_eq!(want, out_gpu.verdicts, "gpu lane disagrees");
            let rns = pack(&b);
            // fold-only (pack amortized out): device path incl. transfers
            let (res2, t_fold) = time(|| g.verify_packed(&b, &rns).expect("gpu packed"));
            assert_eq!(want, res2.0.verdicts, "gpu packed disagrees");
            gpu_cols = (t_gpu, t_fold, res2.1.channels_used);
        }

        // ---- split timings for the FULL device path (table 2) ----
        {
            let nan = f64::NAN;
            // the pre-lever baseline (serial parts+splice spelling) —
            // the receipts' old "pack" number, kept as a column so
            // every table carries its own before/after.
            let (rns_ref, t_packref) = time(|| pack_reference(&b));
            let (rns, t_pack) = time(|| pack(&b));
            assert_eq!(rns, rns_ref, "columnar pack diverged from reference");
            let (req, t_packm) = time(|| pack_membership(&b));
            #[cfg(feature = "parallel")]
            let t_packp = {
                let (rp, t) = time(|| qtsl_geolog_provider_gpu::pack_par(&b));
                assert_eq!(rp, rns, "pack_par != pack");
                t
            };
            #[cfg(not(feature = "parallel"))]
            let t_packp = nan;
            #[cfg(feature = "parallel")]
            let t_packmp = {
                let (rp, t) = time(|| qtsl_geolog_provider_gpu::pack_membership_par(&b));
                assert_eq!(rp, req, "pack_membership_par != pack_membership");
                t
            };
            #[cfg(not(feature = "parallel"))]
            let t_packmp = nan;
            let (_, t_gates) = time(|| {
                (0..b.attempts())
                    .filter(|&a| attempt_gates_exact(&b, a))
                    .count()
            });
            let (out_fullref, t_fullref) = time(|| verify_batch_rns_full(&b));
            assert_eq!(want, out_fullref.verdicts, "full rns reference disagrees");

            #[allow(unused_mut, unused_assignments)]
            let (mut t_folddev, mut t_memb, mut t_full, mut t_fullp) = (nan, nan, nan, nan);
            #[cfg(feature = "cuda")]
            if let Some(g) = &gpu {
                let (fo, t) = time(|| g.fold_only(&rns).expect("fold only"));
                let _ = fo;
                t_folddev = t;
                let (mo, t) = time(|| g.member_only(&req).expect("member only"));
                let _ = mo;
                t_memb = t;
                let (out_full, t) = time(|| {
                    let rns = pack(&b);
                    let req = pack_membership(&b);
                    g.verify_packed_full(&b, &rns, &req).expect("full device")
                });
                assert_eq!(want, out_full.verdicts, "gpu full path disagrees");
                t_full = t;
                #[cfg(feature = "parallel")]
                {
                    let (out_fullp, t) = time(|| {
                        let rns = qtsl_geolog_provider_gpu::pack_par(&b);
                        let req = qtsl_geolog_provider_gpu::pack_membership_par(&b);
                        g.verify_packed_full(&b, &rns, &req)
                            .expect("full device par")
                    });
                    assert_eq!(want, out_fullp.verdicts, "gpu full par path disagrees");
                    t_fullp = t;
                }
            }
            split_rows.push((
                name,
                n,
                entries,
                [
                    t_packref, t_pack, t_packp, t_packm, t_packmp, t_gates, t_fullref, t_folddev,
                    t_memb, t_full, t_fullp,
                ]
                .map(|t| t * 1e6 / inst),
            ));
        }
        if entries >= 200 {
            scaling_batches.push((format!("{name} n={n}"), b.clone()));
        }
        let us = 1e6 / inst;
        println!(
            "{:<40} {:>4} {:>5} | {:>10.1}us {:>10.1}us {:>10.1}us {:>10.1}us {:>10.1}us {:>10}",
            name,
            n,
            entries,
            t_lqq * us,
            t_lint * us,
            t_rns * us,
            gpu_cols.0 * us,
            gpu_cols.1 * us,
            gpu_cols.2,
        );
    }

    // ---- table 2: the full device path, split (µs/instance) ----
    println!();
    println!(
        "{:<40} {:>4} {:>5} | {:>9} {:>9} {:>9} {:>9} {:>9} {:>9} {:>9} {:>9} {:>9} {:>9} {:>9}",
        "shape (full path split)",
        "n",
        "T",
        "pack-ref",
        "pack",
        "packp",
        "packM",
        "packMp",
        "gates",
        "full-ref",
        "fold-dev",
        "memb-dev",
        "full-e2e",
        "full-e2ep"
    );
    for (name, n, t, cols) in split_rows {
        print!("{name:<40} {n:>4} {t:>5} |");
        for c in cols {
            print!(" {c:>8.1}u");
        }
        println!();
    }

    // ---- pack thread-scaling sweep (PACK_SCALING=1, parallel builds) ----
    // min-of-3 per point (pack is deterministic; min discards warmup
    // and scheduler noise — the receipts table says so).
    #[cfg(feature = "parallel")]
    if std::env::var("PACK_SCALING").is_ok() {
        println!();
        println!(
            "pack thread-scaling (min of 3, us/instance; pack-ref = serial parts+splice baseline)"
        );
        for (name, b) in &scaling_batches {
            let inst = b.instances() as f64;
            let us = 1e6 / inst;
            let min3 =
                |f: &mut dyn FnMut() -> f64| (0..3).map(|_| f()).fold(f64::INFINITY, f64::min);
            let t_ref = min3(&mut || time(|| pack_reference(b)).1);
            print!("{name:<50} pack-ref {:>9.1}us |", t_ref * us);
            for threads in [1usize, 2, 4, 8, 12, 16, 24, 32, 48] {
                let pool = rayon::ThreadPoolBuilder::new()
                    .num_threads(threads)
                    .build()
                    .expect("pool");
                let t = min3(&mut || pool.install(|| time(|| pack(b)).1));
                print!(" {threads}t {:>8.1}us", t * us);
            }
            println!();
        }
    }
    #[cfg(not(feature = "parallel"))]
    let _ = scaling_batches;
}
