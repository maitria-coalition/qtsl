//! pin-scoped `CertRows` for the memory down-tier ("TermCols-only"
//! batch mode; the colx receipts' successor 2).
//!
//! The down-tier batch driver runs Phase E entirely off
//! [`crate::blcolx::TermCols`] and never materializes the full
//! [`CertRows`] index (238.9 GB measured at X1 against TermCols'
//! ~5–15 GB projection). What still wants `CertRows` is the eval-pin
//! differential: the E3 evaluator (`blapplic::eval_combo_node_valid`)
//! is the semantically independent implementation the batch verdicts
//! are pinned against, and it reads `CertRows`. This module scopes that
//! need: [`pinned_cert_rows`] builds a `CertRows` restricted to the
//! sub-DAG a walk starting from the given pin roots can reach — built
//! by `CertRows::from_ops` on a FILTERED op subsequence (body order
//! preserved), so the index machinery is the incumbent's own, not a
//! reimplementation.
//!
//! ## Why the filtered index is walk-exact (the visibility argument)
//!
//! The `blapplic::Walk` consults `CertRows` through exactly two
//! reading directions (verified against the source, colx leg + this
//! leg):
//!
//! 1. **producers(e), roster-filtered** (`sole`): every consumer
//!    classifies producer rows against the closed term/formula ctor
//!    rosters and ignores the rest. So for any element `e` the walk
//!    reaches, the filtered index must carry ALL roster-fun rows
//!    producing `e` (ambiguity refusals count them) — non-roster
//!    producers are invisible to `sole` and may be dropped.
//! 2. **arg_rows(node), field-fun-filtered** (`field_opt` /
//!    `indexed_family`): always filtered by a specific non-roster
//!    (field) fun. So for any element the walk reaches, the filtered
//!    index must carry ALL non-roster rows citing it in an argument
//!    position — roster rows in the arg direction are invisible (no
//!    caller filters arg_rows by a roster fun) and may be dropped.
//!
//! The closure below is the least fixpoint of those two rules seeded at
//! the pin roots, with every kept row contributing all its LOCAL
//! element refs (args + value) to the reached set. It over-approximates
//! the walk's actual footprint (fun-blind within each rule; the walk
//! reads specific funs), and over-inclusion is harmless: extra rows are
//! either roster rows reached only downward (exactly what the full
//! index holds) or field rows the fun filters skip. Under-inclusion is
//! what the differential batteries pin (`tests/blcolx.rs`, pinned-rows
//! arms): evaluator verdict/refusal parity and incumbent-extraction
//! plane equality, full rows vs pinned rows, across the fixture corpus
//! and the proptest emitter.
//!
//! Deliberately NOT followed: the constructor-parent direction (a
//! roster row citing a reached element as ARG). Following it would
//! ascend from shared leaves (pooled projections, constants) into every
//! instance touching them — the whole population, defeating the tier.
//! The walk never reads that direction (rule 2's roster exclusion), so
//! its absence is invisible by construction.
//!
//! Attribute-view surfaces (`attrs` / `subject_elems` /
//! `external_subject_rows` — Morse/admission consumers) are NOT scoped
//! by this closure: the filtered index simply reports whatever the kept
//! rows say there. The eval-pin families never consult them; a future
//! consumer that does must widen the closure first (this doc is the
//! contract surface to amend).

use crate::blapplic::BlVocab;
use crate::rowctx::CertRows;
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Value};

/// Build receipts for the pin closure (the down-tier driver's
/// `pin-rows` receipt payload).
#[derive(Debug, Clone, Copy)]
pub struct PinStats {
    /// Total ops scanned.
    pub ops_total: usize,
    /// Fun-value ops kept by the closure (the filtered index's rows).
    pub ops_kept: usize,
    /// Elements in the reached set.
    pub elems_reached: usize,
}

/// A `CertRows` scoped to the sub-DAG reachable from `roots` under the
/// walk-visibility closure (module doc). `own`/`deps` as
/// [`CertRows::from_ops`]; `v` supplies the closed ctor rosters the
/// closure classifies against (the same pinned identities `TermCols`
/// and the incumbent walk use).
pub fn pinned_cert_rows(
    ops: &[Op],
    own: [u8; 32],
    deps: &[[u8; 32]],
    v: &BlVocab,
    roots: &[u32],
) -> (CertRows, PinStats) {
    let term_roster = v.term_ctors();
    let form_roster = v.form_ctors();
    let norm = |r: &ElemRef| -> crate::theory::Chid {
        match r {
            ElemRef::Local(n) => (own, *n),
            ElemRef::External { dep_index, counter } => match deps.get(*dep_index as usize) {
                Some(h) => (*h, *counter),
                None => ([0xFFu8; 32], *counter),
            },
        }
    };

    // ---- pass 1: classify ops, flatten local refs, size the index ----
    // Per fun-value op: roster? (fun in a ctor roster AND local value —
    // the constructor reading `sole` sees), local value elem, local
    // args (deduped — the arg-direction files once per distinct elem,
    // matching CertRows::from_ops).
    const K_NONE: u8 = 0;
    const K_ROSTER: u8 = 1;
    const K_FIELD: u8 = 2;
    let n_ops = ops.len();
    let mut kind = vec![K_NONE; n_ops];
    let mut val_elem = vec![u32::MAX; n_ops];
    let mut arg_off: Vec<u32> = Vec::with_capacity(n_ops + 1);
    let mut arg_flat: Vec<u32> = Vec::new();
    let mut n_elems: usize = 0;
    let mut seen: Vec<u32> = Vec::new();
    for (i, op) in ops.iter().enumerate() {
        arg_off.push(arg_flat.len() as u32);
        let Op::Funa { fun, args, value } = op else {
            continue;
        };
        let local_value = match value {
            Value::Ref(ElemRef::Local(e)) => Some(*e),
            _ => None,
        };
        let fchid = norm(fun);
        let roster = term_roster.contains_key(&fchid) || form_roster.contains_key(&fchid);
        kind[i] = if roster && local_value.is_some() {
            K_ROSTER
        } else {
            K_FIELD
        };
        if let Some(e) = local_value {
            val_elem[i] = e;
            n_elems = n_elems.max(e as usize + 1);
        }
        seen.clear();
        for a in args {
            if let Value::Ref(ElemRef::Local(e)) = a {
                if !seen.contains(e) {
                    seen.push(*e);
                    arg_flat.push(*e);
                    n_elems = n_elems.max(*e as usize + 1);
                }
            }
        }
    }
    arg_off.push(arg_flat.len() as u32);
    for &r in roots {
        n_elems = n_elems.max(r as usize + 1);
    }

    // ---- pass 2: CSR indexes (count + fill) --------------------------
    // prod: elem -> roster ops producing it (rule 1).
    // cite: elem -> field ops citing it in an argument position (rule 2).
    let mut prod_cnt = vec![0u32; n_elems + 1];
    let mut cite_cnt = vec![0u32; n_elems + 1];
    for i in 0..n_ops {
        match kind[i] {
            K_ROSTER => prod_cnt[val_elem[i] as usize + 1] += 1,
            K_FIELD => {
                for j in arg_off[i]..arg_off[i + 1] {
                    cite_cnt[arg_flat[j as usize] as usize + 1] += 1;
                }
            }
            _ => {}
        }
    }
    for e in 0..n_elems {
        prod_cnt[e + 1] += prod_cnt[e];
        cite_cnt[e + 1] += cite_cnt[e];
    }
    let mut prod_ops = vec![0u32; prod_cnt[n_elems] as usize];
    let mut cite_ops = vec![0u32; cite_cnt[n_elems] as usize];
    let mut prod_fill = prod_cnt.clone();
    let mut cite_fill = cite_cnt.clone();
    for i in 0..n_ops {
        match kind[i] {
            K_ROSTER => {
                let e = val_elem[i] as usize;
                prod_ops[prod_fill[e] as usize] = i as u32;
                prod_fill[e] += 1;
            }
            K_FIELD => {
                for j in arg_off[i]..arg_off[i + 1] {
                    let e = arg_flat[j as usize] as usize;
                    cite_ops[cite_fill[e] as usize] = i as u32;
                    cite_fill[e] += 1;
                }
            }
            _ => {}
        }
    }

    // ---- closure (worklist over elements) ----------------------------
    let mut in_set = vec![false; n_elems];
    let mut kept = vec![false; n_ops];
    let mut stack: Vec<u32> = Vec::new();
    for &r in roots {
        if !in_set[r as usize] {
            in_set[r as usize] = true;
            stack.push(r);
        }
    }
    let reach = |e: u32, in_set: &mut Vec<bool>, stack: &mut Vec<u32>| {
        if !in_set[e as usize] {
            in_set[e as usize] = true;
            stack.push(e);
        }
    };
    while let Some(e) = stack.pop() {
        let eu = e as usize;
        // Rule 1: roster rows producing e — keep; descend into args.
        for k in prod_cnt[eu]..prod_cnt[eu + 1] {
            let oi = prod_ops[k as usize] as usize;
            if !kept[oi] {
                kept[oi] = true;
                for j in arg_off[oi]..arg_off[oi + 1] {
                    reach(arg_flat[j as usize], &mut in_set, &mut stack);
                }
            }
        }
        // Rule 2: field rows citing e — keep; reach value + all args.
        for k in cite_cnt[eu]..cite_cnt[eu + 1] {
            let oi = cite_ops[k as usize] as usize;
            if !kept[oi] {
                kept[oi] = true;
                if val_elem[oi] != u32::MAX {
                    reach(val_elem[oi], &mut in_set, &mut stack);
                }
                for j in arg_off[oi]..arg_off[oi + 1] {
                    reach(arg_flat[j as usize], &mut in_set, &mut stack);
                }
            }
        }
    }

    // ---- filtered rebuild (body order preserved) ---------------------
    let filtered: Vec<Op> = ops
        .iter()
        .enumerate()
        .filter(|(i, _)| kept[*i])
        .map(|(_, op)| op.clone())
        .collect();
    let stats = PinStats {
        ops_total: n_ops,
        ops_kept: filtered.len(),
        elems_reached: in_set.iter().filter(|b| **b).count(),
    };
    (CertRows::from_ops(&filtered, own, deps), stats)
}
