//! The promise interface-confinement family: the two `PPromise`
//! side-conditions — `promiseContractConfined` and
//! `promiseWiresSeparated` (S5 in the deferred-grounds census).
//!
//! Spec authority: the Lean catalogue (`Core/Catalogue.lean`) —
//! `PPromiseData`'s two wire obligations:
//!
//! - `contractConfined : formulaWiresWithin contract iface` — every
//!   free wire of the node's contract formula is among its declared
//!   interface wires;
//! - `separation : wiresSeparated supplier.pre ctx seq.post iface` —
//!   every free wire of the supplier's premise that is ALSO free in
//!   the recomputed context `ctx` or in the node's conclusion is among
//!   the interface wires.
//!
//! Both relations receive the node alone (the B11 idiom: the indexed
//! iface family is field access on `p`); every other formula is
//! reached through the node's own field rows.
//!
//! # The recomputed context (the substance of `promiseWiresSeparated`)
//!
//! `ctx` is pinned by the Lean datum
//! `ctxReads : consumer.pre.conjReplace? path .tt = some ctx` — the
//! consumer's premise with the contract slot blanked to `FTrue`. It is
//! RECOMPUTED from the consumer's premise and the node's path rows,
//! never read from any carried formula (designv3's interface-
//! confinement block). At row grain the evaluator never materializes
//! `ctx` (the row context cannot mint elements, and does not need to):
//! `freeWires ctx` is exactly the union of the free wires of the
//! OFF-PATH siblings along the descent — the replaced slot contributes
//! nothing (`FTrue` has no wires) — so the walk collects sibling wire
//! sets while descending the path.
//!
//! # Adjudications (for review eyes)
//!
//! - **Off-tree path = DECIDED FALSE, unconditionally** (including
//!   when the supplier's premise has no free wires, where the Lean
//!   Prop would be vacuously true FOR ANY ctx). "The recomputed
//!   context" is a definite description: when `conjReplace?` returns
//!   `none` there is no such context, and the side-condition fails
//!   closed. Soundness/completeness: in Lean, `ctxReads` is its own
//!   field of `PPromiseData` — a producer with an off-tree path cannot
//!   construct the data at all, so assigning ctx-existence to this
//!   relation preserves the conjunction's total extension (the on-tree
//!   demand is also enforced separately by
//!   `ax/applicable/PPromise/path_reads` via `conjunctAt`). Kin: the
//!   surgery family's off-tree adjudication.
//! - **The conclusion is the NODE's own** — `seq.post`, read through
//!   `p PPromise/proof → Proof/concludes → Judgment/post`. The Lean
//!   `separation` consumes `seq.post`; its equality with the
//!   consumer's post is a SEPARATE datum (`postEq`, enforced by
//!   `ax/applicable/PPromise/post` as a chase equality), never this
//!   relation's to assume.
//! - **Iface is a list, not a set**: `PPromise/ifaceWire` is decoded
//!   with the crate's Index-sort semantics (dense bijective presence
//!   `0..n-1`; duplicates, gaps, out-of-range indices refuse) —
//!   mirroring `iface : List Wire`. Two indices carrying the SAME wire
//!   element are well-formed (a list may repeat); membership is what
//!   the Prop consumes.
//!
//! Verdict discipline (the crate's): a decided wire escape is
//! `Ok(false)`; unresolvable structure — missing/duplicate field rows,
//! unconstructed formula or path elements, cyclic path chains,
//! external refs, malformed iface families — REFUSES with a reason,
//! never guessing.

use crate::atomic::elem_local;
use crate::blsurgery::{decode_path, Dir, SurgeryVocab};
use crate::error::EvalError;
use crate::formrows::{find_field, find_sort, BlVocab, FormCtor, Walk};
use crate::roster::{EntryRow, PromiseKind, RelKind};
use crate::rowctx::CertRows;
use crate::theory::{Chid, TheoryIndex};
use geolog_envelope::Value;
use std::collections::BTreeSet;

// Field names + bytewise order are part of the claim (copied from the
// registry's signature column — both relations are unary on the node).
const F_PROMISE: &[(&str, &str)] = &[("p", "PPromise")];

/// The promise family's rows of the claimed roster (concatenated at
/// registration — provider.rs). Registration order is part of the seam
/// surface: append at the end, never reorder.
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "promiseContractConfined",
        F_PROMISE,
        RelKind::Promise(PromiseKind::ContractConfined),
    ),
    (
        "promiseWiresSeparated",
        F_PROMISE,
        RelKind::Promise(PromiseKind::WiresSeparated),
    ),
];

/// The promise family's resolved vocabulary: the `PPromise` node's
/// field identities, name-selected once at construction and
/// shape-verified (C-ORACLE: names select, shapes verify, identities
/// pin). The Formula/Term/Judgment chain rides the shared [`BlVocab`];
/// the `CtxPath` constructors ride the surgery family's
/// [`SurgeryVocab`] — both passed at evaluation.
#[derive(Debug, Clone)]
pub struct PromiseVocab {
    proof: Chid,
    supplier: Chid,
    consumer: Chid,
    contract: Chid,
    path: Chid,
    n_iface_wires: Chid,
    iface_wire: Chid,
}

/// Build the promise vocabulary over the declared indices. `Err` → the
/// family is not claimed (declared-but-unbound, safe-fail).
pub fn build_promise_vocab(indices: &[&TheoryIndex]) -> Result<PromiseVocab, String> {
    let p = find_sort(indices, "PPromise")?;
    Ok(PromiseVocab {
        proof: find_field(indices, "PPromise/proof", p)?,
        supplier: find_field(indices, "PPromise/supplier", p)?,
        consumer: find_field(indices, "PPromise/consumer", p)?,
        contract: find_field(indices, "PPromise/contract", p)?,
        path: find_field(indices, "PPromise/path", p)?,
        n_iface_wires: find_field(indices, "PPromise/nIfaceWires", p)?,
        iface_wire: find_field(indices, "PPromise/ifaceWire", p)?,
    })
}

/// Evaluate a promise-family relation. One argument cell: the
/// `PPromise` node element.
pub(crate) fn eval_promise(
    name: &str,
    v: &BlVocab,
    pv: &PromiseVocab,
    sv: &SurgeryVocab,
    kind: PromiseKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, v, rows);
    let p = elem_local(name, 0, args[0], rows)?;

    // The declared interface: `nIfaceWires` + the dense indexed family
    // (bijective presence 0..n-1; duplicates/gaps/out-of-range refuse).
    let n = w.field_nat(0, p, pv.n_iface_wires, "PPromise/nIfaceWires")?;
    let iface: BTreeSet<u32> = w
        .indexed_family(0, p, pv.iface_wire, n, "PPromise/ifaceWire")?
        .into_iter()
        .collect();

    match kind {
        PromiseKind::ContractConfined => {
            // formulaWiresWithin contract iface.
            let contract = w.field_elem(0, p, pv.contract, "PPromise/contract")?;
            let mut free = BTreeSet::new();
            w.formula_free_wires(0, contract, &mut free)?;
            Ok(free.iter().all(|fw| iface.contains(fw)))
        }
        PromiseKind::WiresSeparated => {
            // wiresSeparated supplier.pre ctx seq.post iface, with ctx
            // recomputed from the consumer's premise + the path.
            let (pc, jpre, jpost) = v.concludes_chids();
            let supplier = w.field_elem(0, p, pv.supplier, "PPromise/supplier")?;
            let sj = w.field_elem(0, supplier, pc, "Proof/concludes")?;
            let sup_pre = w.field_elem(0, sj, jpre, "Judgment/pre")?;

            let consumer = w.field_elem(0, p, pv.consumer, "PPromise/consumer")?;
            let cj = w.field_elem(0, consumer, pc, "Proof/concludes")?;
            let cons_pre = w.field_elem(0, cj, jpre, "Judgment/pre")?;

            // seq.post — the node's OWN conclusion (adjudication above).
            let proof = w.field_elem(0, p, pv.proof, "PPromise/proof")?;
            let nj = w.field_elem(0, proof, pc, "Proof/concludes")?;
            let post = w.field_elem(0, nj, jpost, "Judgment/post")?;

            // The recomputed context's free wires: descend the path
            // through the consumer's premise, collecting each off-path
            // sibling's free wires; the replaced slot (blanked to
            // FTrue) contributes nothing. A non-FAnd node under a
            // remaining step means `conjReplace? = none`: no recomputed
            // context exists — decidedly false (adjudication above).
            let path = w.field_elem(0, p, pv.path, "PPromise/path")?;
            let dirs = decode_path(name, &mut w, sv, rows, 0, path)?;
            let mut ctx_free = BTreeSet::new();
            let mut cur = cons_pre;
            for d in dirs {
                let (k, row) = w.form_ctor_row(0, cur)?;
                if k != FormCtor::And {
                    return Ok(false);
                }
                let (descend, keep) = match d {
                    Dir::Left => (0, 1),
                    Dir::Right => (1, 0),
                };
                let sibling = w.local(0, &row.args[keep])?;
                w.formula_free_wires(0, sibling, &mut ctx_free)?;
                cur = w.local(0, &row.args[descend])?;
            }
            // `conjReplace? .here g = some g` regardless of the
            // replaced subtree's shape: the slot's prior content is
            // unconstrained and unread (the surgery family's reading).
            let _ = cur;

            let mut sup_free = BTreeSet::new();
            w.formula_free_wires(0, sup_pre, &mut sup_free)?;
            let mut post_free = BTreeSet::new();
            w.formula_free_wires(0, post, &mut post_free)?;

            Ok(sup_free.iter().all(|fw| {
                let shared = ctx_free.contains(fw) || post_free.contains(fw);
                !shared || iface.contains(fw)
            }))
        }
    }
}
