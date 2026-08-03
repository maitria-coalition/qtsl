//! `qtsl_kcite_wf` / `qtsl_gate_scalar` + the kernel-citation circuit
//! arms of `qtsl_tr_grain` / `qtsl_tr_endo`: the store-seam walks —
//! evaluators whose subject cites a hypernet by digest, so evaluation
//! reaches through the [`crate::store`] seam for the cited bytes and
//! decodes them with the org's one canonical decoder
//! (`maitria-hypernet`, the AXHN0001 codec).
//!
//! Semantic authority: the Qtsl theory's KernelCite block
//! (`mkKernelCite`, the C-JD-KCITE demand `qtsl_kcite_wf`), the gate
//! conformance demand beside `oGate` ("every gate citation resolves to
//! a scalar-codomain hypernet … checked at admission, where the cited
//! content is reachable" — `qtsl_gate_scalar`), and the Transition
//! former's grain/endo demands on kernel-citation content. The walks
//! port the driver-local `atari_provider.rs` evaluators from the
//! producer-side toolkit, whose header names this port as
//! its own residue; the walk-evaluator design memo (F-3…F-6) is
//! the binding design.
//!
//! # Verdict semantics (carried over from inc-2 verbatim)
//!
//! - an ABSENT store object REFUSES ("unreachable content is never
//!   guessed" — and a provider with no store attached refuses every
//!   instance with that case named, while its CLAIMS stay
//!   vocabulary-gated: loud beats silent);
//! - a store object that does not decode canonically DECIDES FALSE
//!   with the decode branch named;
//! - a digest recompute that disagrees with the citation DECIDES
//!   FALSE with the digest branch named. Decode and digest are
//!   DISTINCT gates (the inc-2 topo-swap lesson: batteries keep a
//!   guaranteed decoder-branch specimen separate from digest-branch
//!   specimens).
//!
//! Decided violations surface through the provider's named-violations
//! register (design memo F-4): the dispatch pushes `"<relation>:
//! <why>"` at every decided-false, and
//! [`crate::QtslGroundProvider::take_violations`] drains it.
//!
//! # The walks
//!
//! **`qtsl_kcite_wf {k}`** (C-JD-KCITE): decode-then-digest against
//! the cited store object, then the roster/arity/typing discipline —
//! tag positions (`next`/`stay`/`cemetery`) pairwise distinct, within
//! the decoded output arity, one-hot Boolean scalar wires; the noise
//! roster strictly ascending within the input arity; the payload
//! positional (every non-tag output a rational scalar); the image box
//! well-formed (interval order + nonnegative floor — its width tie is
//! the endo check's).
//!
//! **circuit `qtsl_tr_grain {sys, tr}`**: the kernel-citation
//! fragment (grWhole grain + `tr_kernel` row): the decoded input
//! arity ties to the declared state block (the `mech_init_box` arity
//! witness) plus the noise roster's fresh draws.
//!
//! **circuit `qtsl_tr_endo {sys, tr}`**: the decoded output interface
//! endo-ties to the state block — three tag wires plus one payload
//! scalar per coordinate — and the landing enclosure carries exactly
//! one interval per coordinate.
//!
//! **`qtsl_gate_scalar {gate}`**: decode + digest tie, then the
//! codomain demand — exactly one output wire of scalar shape and
//! rational kind. Zero/many outputs and non-rational-scalar codomains
//! decide FALSE named; a Boolean scalar codomain REFUSES with the
//! case named (the sign-fiber vs {0,∞}-face reading is not this
//! leg's to decide — the design memo's adjudication).
//!
//! Routing note: `qtsl_tr_grain`/`qtsl_tr_endo` KEEP their single
//! roster entries in the trwf family — the provider dispatch routes a
//! kernel-citation transition (a `tr_kernel` row on `tr`) to these
//! walks and every other shape to the landed P/T walk, untouched
//! (`crate::trwf`); where the circuit vocabulary did not resolve, the
//! P/T walk's refusal of kernel content remains the loud deferral.

use crate::qq::QQ;
use crate::roster::{CircuitKind, EntryRow, RelKind};
use crate::rowctx::{CertRows, CtorRow};
use crate::store::StoreResolver;
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{ElemRef, LiteralView, Value};
use maitria_hypernet::{Hypernet, Kind};
use std::collections::{HashMap, HashSet};
use std::sync::Mutex;

/// The store-seam family's NEW rows of the claimed roster
/// (concatenated at registration — provider.rs; appended LAST so
/// every existing roster position is unchanged).
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "qtsl_kcite_wf",
        &[("k", "KernelCite")],
        RelKind::Circuit(CircuitKind::KciteWf),
    ),
    (
        "qtsl_gate_scalar",
        &[("gate", "HypernetRef")],
        RelKind::Circuit(CircuitKind::GateScalar),
    ),
];

// ---------------------------------------------------------------------
// Vocabulary
// ---------------------------------------------------------------------

/// The kernel-citation circuit vocabulary, pinned at vocabulary
/// resolution (names select, shapes verify, identities pin). The
/// roster is the driver's `CircuitIds`, ported; every name is
/// witnessed against the theory source (`theories/Qtsl.geolog`):
/// `mkInterval`/`boxNil`/`boxCons` (the Box kit), `hnDigest`
/// (HypernetRef), `mkKernelCite`/`KernelCite`, `grWhole`,
/// `Transition/grain`, `tr_kernel` (bytewise (kernel, tr)),
/// `mech_init_box` (bytewise (box, mech)), `SysMech`.
#[derive(Debug, Clone)]
pub struct CircuitVocab {
    mk_kcite: Chid,
    hn_digest: Chid,
    sys_mech: Chid,
    gr_whole: Chid,
    /// `Transition/grain` — the exactly-one grain attribute.
    tr_grain: Chid,
    tr_kernel: Chid,
    mech_init_box: Chid,
    box_nil: Chid,
    box_cons: Chid,
    interval_mk: Chid,
}

/// The gate-scalar vocabulary: `qtsl_gate_scalar`'s subject is the
/// `HypernetRef` itself, so the walk reads exactly one constructor —
/// `hnDigest` — and nothing else (`oGate` is the *demand's* trigger
/// in the theory's chase row, not vocabulary this evaluator reads;
/// requiring it here would couple the family to the observable grid
/// it never walks).
#[derive(Debug, Clone)]
pub struct GateScalarVocab {
    hn_digest: Chid,
}

/// A fun by name across the swept indices (constructor vs relation
/// per `relational`), cross-revision ambiguity refused — never picked
/// through (the swret resolver's rule). `pub(crate)` so that the
/// dwell-gate/ratecap families can reuse the store-seam
/// resolution and row helpers rather than re-transcribing them.
pub(crate) fn find_fun(
    indices: &[&TheoryIndex],
    name: &str,
    relational: bool,
) -> Result<(Chid, DomainSig, Option<SortKey>), String> {
    let mut found: Option<(Chid, DomainSig, Option<SortKey>)> = None;
    for index in indices {
        if let Some(d) = index.fun(name) {
            if d.relational != relational {
                return Err(format!(
                    "`{name}`: expected {} declaration",
                    if relational { "a relational" } else { "a fun" }
                ));
            }
            match &found {
                None => found = Some((d.chid, d.domain.clone(), d.codomain)),
                Some((f, _, _)) if *f == d.chid => {}
                Some(_) => {
                    return Err(format!(
                        "`{name}` names two distinct declarations across the \
                         swept revisions — ambiguous, refusing to pick"
                    ))
                }
            }
        }
    }
    found.ok_or_else(|| format!("no `{name}` declaration among the swept revisions"))
}

/// A sort by name across the swept indices, ambiguity refused.
pub(crate) fn find_sort(indices: &[&TheoryIndex], name: &str) -> Result<Chid, String> {
    let mut found: Option<Chid> = None;
    for index in indices {
        if let Some(c) = index.sort(name) {
            match found {
                None => found = Some(c),
                Some(f) if f == c => {}
                Some(_) => {
                    return Err(format!(
                        "`{name}` names two distinct sorts across the swept \
                         revisions — ambiguous, refusing to pick"
                    ))
                }
            }
        }
    }
    found.ok_or_else(|| format!("no `{name}` sort among the swept revisions"))
}

/// One expected record field: its bytewise (wire) name plus the
/// sort-shape check.
type FieldCheck<'a> = (&'a str, &'a dyn Fn(&SortKey) -> bool);

/// A KernelCite's decoded fields, in declaration order:
/// (cemetery, digest hex, image box elem, next, noise, stay).
type KciteFields = (u64, String, u32, u64, Vec<u64>, u64);

/// The declared record fields, verified against `(name, check)` pairs
/// in bytewise (wire) order.
fn verify_record(
    sig: &DomainSig,
    what: &str,
    want: &[FieldCheck<'_>],
) -> Result<Vec<SortKey>, String> {
    let DomainSig::Record(fields) = sig else {
        return Err(format!("`{what}`: expected a record domain"));
    };
    if fields.len() != want.len() {
        return Err(format!("`{what}`: expected {} record fields", want.len()));
    }
    for ((n, s), (wn, wf)) in fields.iter().zip(want.iter()) {
        if n != wn || !wf(s) {
            return Err(format!(
                "`{what}`: field `{n}` has an unexpected name or sort"
            ));
        }
    }
    Ok(fields.iter().map(|(_, s)| *s).collect())
}

/// Resolve `hnDigest : {sha256hex: Str} -> HypernetRef` (shared by
/// both groups; each resolves it independently so the families gate
/// independently).
pub(crate) fn resolve_hn_digest(indices: &[&TheoryIndex]) -> Result<(Chid, Chid), String> {
    let hypref_sort = find_sort(indices, "HypernetRef")?;
    let (hn_digest, sig, cod) = find_fun(indices, "hnDigest", false)?;
    if cod != Some(SortKey::Elem(hypref_sort)) {
        return Err("`hnDigest`: codomain is not the HypernetRef sort".into());
    }
    let is_str = |s: &SortKey| *s == SortKey::Ground(Ground::Str);
    verify_record(&sig, "hnDigest", &[("sha256hex", &is_str)])?;
    Ok((hn_digest, hypref_sort))
}

/// Build the kernel-citation circuit vocabulary over the declared
/// indices. `Err` → the family is not claimed (declared-but-unbound,
/// safe-fail; reason recorded on the provider's vocabulary notes) —
/// in particular, every closure predating the KernelCite block lacks
/// `mkKernelCite` and the family correctly does not resolve there.
pub fn build_circuit_vocab(indices: &[&TheoryIndex]) -> Result<CircuitVocab, String> {
    let is_nat = |s: &SortKey| *s == SortKey::Ground(Ground::Nat);
    let is_q = |s: &SortKey| *s == SortKey::Ground(Ground::Q);
    let is_shape = |s: &SortKey| *s == SortKey::Ground(Ground::Shape);
    let is_elem_eq = |want: Chid| move |s: &SortKey| *s == SortKey::Elem(want);
    let is_elem = |s: &SortKey| matches!(s, SortKey::Elem(_));

    let (hn_digest, hypref_sort) = resolve_hn_digest(indices)?;
    let kernelcite_sort = find_sort(indices, "KernelCite")?;
    let box_sort = find_sort(indices, "Box")?;
    let interval_sort = find_sort(indices, "Interval")?;

    // mkKernelCite : {cemetery: Nat, hypernet: HypernetRef, image: Box,
    //                 next: Nat, noise: Shape, stay: Nat} -> KernelCite
    // (fields already in bytewise order in the source).
    let (mk_kcite, sig, cod) = find_fun(indices, "mkKernelCite", false)?;
    if cod != Some(SortKey::Elem(kernelcite_sort)) {
        return Err("`mkKernelCite`: codomain is not the KernelCite sort".into());
    }
    verify_record(
        &sig,
        "mkKernelCite",
        &[
            ("cemetery", &is_nat),
            ("hypernet", &is_elem_eq(hypref_sort)),
            ("image", &is_elem_eq(box_sort)),
            ("next", &is_nat),
            ("noise", &is_shape),
            ("stay", &is_nat),
        ],
    )?;

    // The Box kit: boxNil / boxCons {head: Interval, tail: Box} /
    // mkInterval {hi: Q, lo: Q}.
    let (box_nil, sig, cod) = find_fun(indices, "boxNil", false)?;
    if sig != DomainSig::Nullary || cod != Some(SortKey::Elem(box_sort)) {
        return Err("`boxNil`: expected a nullary Box constructor".into());
    }
    let (box_cons, sig, cod) = find_fun(indices, "boxCons", false)?;
    if cod != Some(SortKey::Elem(box_sort)) {
        return Err("`boxCons`: codomain is not the Box sort".into());
    }
    verify_record(
        &sig,
        "boxCons",
        &[
            ("head", &is_elem_eq(interval_sort)),
            ("tail", &is_elem_eq(box_sort)),
        ],
    )?;
    let (interval_mk, sig, cod) = find_fun(indices, "mkInterval", false)?;
    if cod != Some(SortKey::Elem(interval_sort)) {
        return Err("`mkInterval`: codomain is not the Interval sort".into());
    }
    verify_record(&sig, "mkInterval", &[("hi", &is_q), ("lo", &is_q)])?;

    // SysMech : {mech: Mech} -> System (the mech sort derived from the
    // field — the walk never names it).
    let (sys_mech, sig, _cod) = find_fun(indices, "SysMech", false)?;
    let fields = verify_record(&sig, "SysMech", &[("mech", &is_elem)])?;
    let SortKey::Elem(mech_sort) = fields[0] else {
        unreachable!("verified an element field")
    };

    // Transition/grain : Transition -> TrGrain (exactly-one attribute;
    // the transition and grain sorts derived from its signature).
    let (tr_grain, sig, cod) = find_fun(indices, "Transition/grain", false)?;
    let DomainSig::Unary(SortKey::Elem(transition_sort)) = sig else {
        return Err("`Transition/grain`: expected a unary attribute on its subject sort".into());
    };
    let Some(SortKey::Elem(grain_sort)) = cod else {
        return Err("`Transition/grain` has no element codomain".into());
    };

    // grWhole : TrGrain (nullary — the whole-coordinate-block grain).
    let (gr_whole, sig, cod) = find_fun(indices, "grWhole", false)?;
    if sig != DomainSig::Nullary || cod != Some(SortKey::Elem(grain_sort)) {
        return Err("`grWhole`: expected a nullary TrGrain constructor".into());
    }

    // tr_kernel : {kernel: KernelCite, tr: Transition} (bytewise).
    let (tr_kernel, sig, cod) = find_fun(indices, "tr_kernel", true)?;
    if cod.is_some() {
        return Err("`tr_kernel`: expected a relation (no codomain)".into());
    }
    verify_record(
        &sig,
        "tr_kernel",
        &[
            ("kernel", &is_elem_eq(kernelcite_sort)),
            ("tr", &is_elem_eq(transition_sort)),
        ],
    )?;

    // mech_init_box : {box: Box, mech: Mech} (bytewise).
    let (mech_init_box, sig, cod) = find_fun(indices, "mech_init_box", true)?;
    if cod.is_some() {
        return Err("`mech_init_box`: expected a relation (no codomain)".into());
    }
    verify_record(
        &sig,
        "mech_init_box",
        &[
            ("box", &is_elem_eq(box_sort)),
            ("mech", &is_elem_eq(mech_sort)),
        ],
    )?;

    Ok(CircuitVocab {
        mk_kcite,
        hn_digest,
        sys_mech,
        gr_whole,
        tr_grain,
        tr_kernel,
        mech_init_box,
        box_nil,
        box_cons,
        interval_mk,
    })
}

/// Build the gate-scalar vocabulary (its own group: the family gates
/// on `hnDigest`/`HypernetRef` alone, independent of the KernelCite
/// block).
pub fn build_gatescalar_vocab(indices: &[&TheoryIndex]) -> Result<GateScalarVocab, String> {
    let (hn_digest, _hypref) = resolve_hn_digest(indices)?;
    Ok(GateScalarVocab { hn_digest })
}

// ---------------------------------------------------------------------
// The store context: fetch + decode + digest, cached per digest
// ---------------------------------------------------------------------

/// The decoded interface summary of one cited store object — the
/// driver's `DecodedStore` shape: input/output arities plus, per
/// output position, `(is_bool_scalar, is_rat_scalar)`.
#[derive(Debug, Clone)]
pub(crate) struct CachedDecode {
    inputs: usize,
    outputs: usize,
    out_kinds: Vec<(bool, bool)>,
}

/// The provider's per-digest decode cache (one container cites one
/// netlist from several claim rows — the atari measurement). `Mutex`
/// rather than `RefCell`: the provider is one shared value (statics
/// in the test fixtures; potentially threads at an engine host), and
/// the seam declares no `Send`/`Sync` bounds either way.
pub(crate) type DecodeCache = Mutex<HashMap<String, Result<CachedDecode, String>>>;

/// The store-seam evaluation context the provider dispatch hands the
/// walks: the attached store (if any) and the decode cache.
pub(crate) struct StoreCtx<'a> {
    pub store: Option<&'a dyn StoreResolver>,
    pub cache: &'a DecodeCache,
}

impl StoreCtx<'_> {
    /// Resolve + decode the store object cited by `hex`. Decode
    /// failure and digest mismatch are DECIDED violations (`Ok(Err)`,
    /// distinct messages — the two gates stay separate); unreachable
    /// content REFUSES (`Err`) — a missing object, or no store
    /// attached at all, is never guessed over.
    fn decoded(&self, hex: &str) -> Result<Result<CachedDecode, String>, String> {
        if let Some(hit) = self.cache.lock().expect("decode cache lock").get(hex) {
            return Ok(hit.clone());
        }
        let Some(store) = self.store else {
            return Err("cited content unreachable — no store attached".into());
        };
        let Some(bytes) = store.fetch(hex) else {
            return Err(format!(
                "store object {hex} unreachable — refusing over guessing"
            ));
        };
        let verdict = (|| -> Result<CachedDecode, String> {
            let h = Hypernet::from_canonical_bytes(&bytes)
                .map_err(|e| format!("store object does not decode canonically: {e:?}"))?;
            let re = h
                .digest()
                .map_err(|e| format!("digest recompute: {e:?}"))?
                .to_hex();
            if re != hex {
                return Err(format!(
                    "digest recompute {re} disagrees with the citation {hex}"
                ));
            }
            let mut out_kinds = Vec::with_capacity(h.graph_outputs.len());
            for &w in &h.graph_outputs {
                // Unreachable after a canonical decode (the codec
                // validates wire references); decided rather than
                // panicked if it ever were.
                let t = h.wtype(w).ok_or_else(|| {
                    format!("store object output wire {w} is untyped — malformed decode")
                })?;
                let scalar = t.shape.is_empty();
                out_kinds.push((
                    scalar && t.dtype.kind == Kind::Bool,
                    scalar && t.dtype.kind == Kind::Rat,
                ));
            }
            Ok(CachedDecode {
                inputs: h.graph_inputs.len(),
                outputs: h.graph_outputs.len(),
                out_kinds,
            })
        })();
        self.cache
            .lock()
            .expect("decode cache lock")
            .insert(hex.to_string(), verdict.clone());
        Ok(verdict)
    }
}

// ---------------------------------------------------------------------
// Row helpers (the driver walk's, ported; refusals as `Err(String)`)
// ---------------------------------------------------------------------

pub(crate) fn local_elem(rows: &CertRows, v: &Value) -> Result<u32, String> {
    match v {
        Value::Ref(r) => rows
            .local(r)
            .ok_or_else(|| "element ref is not body-local".to_string()),
        _ => Err("expected an element ref".into()),
    }
}

/// The element's one constructor row AMONG the expected roster
/// (byte-identical rows are one row — the trwf family's set-semantic
/// counting; distinct roster rows refuse).
pub(crate) fn producer_in<'a>(
    rows: &'a CertRows,
    elem: u32,
    roster: &[Chid],
    what: &str,
) -> Result<&'a CtorRow, String> {
    let mut found: Option<&CtorRow> = None;
    for r in rows.producers(elem) {
        if !roster.contains(&r.fun) {
            continue;
        }
        match found {
            None => found = Some(r),
            Some(f) => {
                if r.fun != f.fun || r.args != f.args || r.value != f.value {
                    return Err(format!(
                        "{what}: element {elem} has distinct constructor rows"
                    ));
                }
            }
        }
    }
    found.ok_or_else(|| format!("{what}: element {elem} has no expected constructor row"))
}

fn nat_lit(v: &Value, what: &str) -> Result<u64, String> {
    if let Value::Lit(l) = v {
        if let LiteralView::Nat(n) = l.view() {
            return Ok(n);
        }
    }
    Err(format!("{what}: not a Nat literal"))
}

pub(crate) fn str_lit(v: &Value, what: &str) -> Result<String, String> {
    if let Value::Lit(l) = v {
        if let LiteralView::Str(s) = l.view() {
            return Ok(s.to_string());
        }
    }
    Err(format!("{what}: not a Str literal"))
}

fn shape_lit(v: &Value, what: &str) -> Result<Vec<u64>, String> {
    if let Value::Lit(l) = v {
        if let LiteralView::Shape(s) = l.view() {
            return Ok(s.iter().collect());
        }
    }
    Err(format!("{what}: not a Shape literal"))
}

pub(crate) fn q_lit(v: &Value, what: &str) -> Result<QQ, String> {
    if let Value::Lit(l) = v {
        if let Some(q) = QQ::from_q_literal(l) {
            return Ok(q);
        }
    }
    Err(format!("{what}: not a Q literal"))
}

impl CircuitVocab {
    /// Whether `tr` carries any `tr_kernel` row — the provider
    /// dispatch's routing probe for the grain/endo circuit arms.
    /// Anything undecodable answers `false`, so the P/T walk states
    /// the refusal on its own terms.
    pub(crate) fn cites_kernel(&self, rows: &CertRows, tr_arg: &Value) -> bool {
        let Ok(tr) = local_elem(rows, tr_arg) else {
            return false;
        };
        let target = Value::Ref(ElemRef::Local(tr));
        rows.rel_rows_citing(tr)
            .iter()
            .any(|r| r.rel == self.tr_kernel && r.args.get(1) == Some(&target))
    }

    /// Walk a box spine; returns the interval count, checking each
    /// interval's order (`lo <= hi`) and floor (`lo >= 0` — the
    /// Boolean box's coordinates are nonnegative).
    fn walk_box(&self, rows: &CertRows, mut elem: u32, what: &str) -> Result<usize, String> {
        let mut n = 0usize;
        let mut seen = HashSet::new();
        loop {
            if !seen.insert(elem) {
                return Err(format!("{what}: cyclic box spine"));
            }
            let row = producer_in(rows, elem, &[self.box_nil, self.box_cons], what)?;
            if row.fun == self.box_nil {
                return Ok(n);
            }
            // boxCons args bytewise: (head interval, tail).
            let iv = local_elem(rows, &row.args[0])?;
            let ivr = producer_in(rows, iv, &[self.interval_mk], what)?;
            // mkInterval args bytewise: (hi, lo).
            let hi = q_lit(&ivr.args[0], &format!("{what}: interval hi"))?;
            let lo = q_lit(&ivr.args[1], &format!("{what}: interval lo"))?;
            if lo.cmp_qq(&hi) == std::cmp::Ordering::Greater {
                return Err(format!("{what}: interval lo > hi"));
            }
            if !lo.is_nonneg() {
                return Err(format!("{what}: interval lo < 0"));
            }
            n += 1;
            elem = local_elem(rows, &row.args[1])?;
        }
    }

    /// The KernelCite element's fields, resolved through the rows:
    /// (cemetery, digest hex, image box elem, next, noise, stay).
    fn kcite_fields(&self, rows: &CertRows, kc: u32) -> Result<KciteFields, String> {
        let row = producer_in(rows, kc, &[self.mk_kcite], "kcite")?;
        // Args bytewise: cemetery, hypernet, image, next, noise, stay.
        let cemetery = nat_lit(&row.args[0], "kcite/cemetery")?;
        let hn = local_elem(rows, &row.args[1])?;
        let hnr = producer_in(rows, hn, &[self.hn_digest], "kcite/hypernet")?;
        let hex = str_lit(&hnr.args[0], "hnDigest/sha256hex")?;
        let image = local_elem(rows, &row.args[2])?;
        let next = nat_lit(&row.args[3], "kcite/next")?;
        let noise = shape_lit(&row.args[4], "kcite/noise")?;
        let stay = nat_lit(&row.args[5], "kcite/stay")?;
        Ok((cemetery, hex, image, next, noise, stay))
    }

    /// The transition's KernelCite element (via the tr_kernel row
    /// citing it).
    fn tr_kcite(&self, rows: &CertRows, tr: u32) -> Result<u32, String> {
        // tr_kernel args bytewise: (kernel, tr).
        let mut kc = None;
        for r in rows.rel_rows_citing(tr) {
            if r.rel == self.tr_kernel && local_elem(rows, &r.args[1])? == tr {
                if kc.is_some() {
                    return Err("two tr_kernel rows for one transition".into());
                }
                kc = Some(local_elem(rows, &r.args[0])?);
            }
        }
        kc.ok_or_else(|| "no tr_kernel row (kernel-citation fragment)".into())
    }

    /// The attached system's state-block width witness: the mech's
    /// init box arity (`mech_init_box`, bytewise (box, mech)).
    fn state_width(&self, rows: &CertRows, sys: u32) -> Result<usize, String> {
        let sysr = producer_in(rows, sys, &[self.sys_mech], "sys")?;
        let mech = local_elem(rows, &sysr.args[0])?;
        let mut width = None;
        for r in rows.rel_rows_citing(mech) {
            if r.rel == self.mech_init_box && local_elem(rows, &r.args[1])? == mech {
                if width.is_some() {
                    return Err("two init-box rows for one mechanism".into());
                }
                let bx = local_elem(rows, &r.args[0])?;
                width = Some(self.walk_box(rows, bx, "init box")?);
            }
        }
        width.ok_or_else(|| "no init-box row: the state block has no width witness".into())
    }

    /// Whether the transition's grain is `grWhole` (the circuit
    /// fragment's only lawful grain).
    fn grain_is_whole(&self, rows: &CertRows, tr: u32) -> Result<bool, String> {
        for a in rows.attrs(tr) {
            if a.fun == self.tr_grain {
                let g = local_elem(rows, &a.value)?;
                return Ok(producer_in(rows, g, &[self.gr_whole], "grain").is_ok());
            }
        }
        Err("no Transition/grain row".into())
    }

    /// `qtsl_kcite_wf {k}` — C-JD-KCITE (module doc). `Ok(Ok(()))`
    /// holds, `Ok(Err(why))` decides false WITH the named violation,
    /// `Err(refuse)` refuses.
    pub(crate) fn eval_kcite_wf(
        &self,
        ctx: &StoreCtx<'_>,
        args: &[&Value],
        rows: &CertRows,
    ) -> Result<Result<(), String>, String> {
        let kc = local_elem(rows, args[0])?;
        let (cemetery, hex, image, next, noise, stay) = self.kcite_fields(rows, kc)?;
        let dec = match ctx.decoded(&hex)? {
            Ok(d) => d,
            Err(fail) => return Ok(Err(fail)),
        };
        // C-JD-KCITE: tags pairwise distinct, within the output
        // arity, one-hot Boolean-typed; noise strictly ascending
        // within the input arity; payload positional (the remaining
        // outputs, scalar-typed).
        if next == stay || next == cemetery || stay == cemetery {
            return Ok(Err("tag positions coincide".into()));
        }
        for (name, t) in [("next", next), ("stay", stay), ("cemetery", cemetery)] {
            if t as usize >= dec.outputs {
                return Ok(Err(format!("tag {name} out of the output arity")));
            }
            if !dec.out_kinds[t as usize].0 {
                return Ok(Err(format!("tag {name} is not a Boolean scalar wire")));
            }
        }
        for w in noise.windows(2) {
            if w[0] >= w[1] {
                return Ok(Err("noise roster not strictly ascending".into()));
            }
        }
        if let Some(&last) = noise.last() {
            if last as usize >= dec.inputs {
                return Ok(Err("noise roster exceeds the input arity".into()));
            }
        }
        let tags = [next as usize, stay as usize, cemetery as usize];
        for (pos, kinds) in dec.out_kinds.iter().enumerate() {
            if !tags.contains(&pos) && !kinds.1 {
                return Ok(Err(format!(
                    "payload output {pos} is not a rational scalar wire"
                )));
            }
        }
        // The image box is citation data: well-formed intervals
        // (order + floor); its width tie against the payload is the
        // endo check's.
        match self.walk_box(rows, image, "image box") {
            Ok(_) => Ok(Ok(())),
            Err(why) => Ok(Err(why)),
        }
    }

    /// The circuit arm of `qtsl_tr_grain {sys, tr}` (module doc).
    pub(crate) fn eval_circuit_grain(
        &self,
        ctx: &StoreCtx<'_>,
        args: &[&Value],
        rows: &CertRows,
    ) -> Result<Result<(), String>, String> {
        // Args bytewise: (sys, tr).
        let sys = local_elem(rows, args[0])?;
        let tr = local_elem(rows, args[1])?;
        if !self.grain_is_whole(rows, tr)? {
            return Err("grain is not grWhole (circuit fragment)".into());
        }
        let width = self.state_width(rows, sys)?;
        let kc = self.tr_kcite(rows, tr)?;
        let (_, hex, _, _, noise, _) = self.kcite_fields(rows, kc)?;
        let dec = match ctx.decoded(&hex)? {
            Ok(d) => d,
            Err(fail) => return Ok(Err(fail)),
        };
        // grWhole: the kernel's input block IS the state block (plus
        // the noise roster's fresh draws).
        if dec.inputs != width + noise.len() {
            return Ok(Err(format!(
                "kernel input arity {} vs state width {width} + noise {}",
                dec.inputs,
                noise.len()
            )));
        }
        Ok(Ok(()))
    }

    /// The circuit arm of `qtsl_tr_endo {sys, tr}` (module doc).
    pub(crate) fn eval_circuit_endo(
        &self,
        ctx: &StoreCtx<'_>,
        args: &[&Value],
        rows: &CertRows,
    ) -> Result<Result<(), String>, String> {
        let sys = local_elem(rows, args[0])?;
        let tr = local_elem(rows, args[1])?;
        let width = self.state_width(rows, sys)?;
        let kc = self.tr_kcite(rows, tr)?;
        let (_, hex, image, _, _, _) = self.kcite_fields(rows, kc)?;
        let dec = match ctx.decoded(&hex)? {
            Ok(d) => d,
            Err(fail) => return Ok(Err(fail)),
        };
        // The payload (outputs minus the three tags) is typed at the
        // system's state: one scalar per coordinate.
        if dec.outputs != 3 + width {
            return Ok(Err(format!(
                "kernel payload {} vs state width {width}",
                dec.outputs.saturating_sub(3)
            )));
        }
        // The landing enclosure carries exactly `width` intervals.
        let ivs = self.walk_box(rows, image, "image box")?;
        if ivs != width {
            return Ok(Err(format!(
                "landing enclosure {ivs} intervals vs state width {width}"
            )));
        }
        Ok(Ok(()))
    }
}

impl GateScalarVocab {
    /// `qtsl_gate_scalar {gate}` — decode + digest tie + the codomain
    /// demand (module doc).
    pub(crate) fn eval_gate_scalar(
        &self,
        ctx: &StoreCtx<'_>,
        args: &[&Value],
        rows: &CertRows,
    ) -> Result<Result<(), String>, String> {
        let gate = local_elem(rows, args[0])?;
        let r = producer_in(rows, gate, &[self.hn_digest], "gate")?;
        let hex = str_lit(&r.args[0], "hnDigest/sha256hex")?;
        let dec = match ctx.decoded(&hex)? {
            Ok(d) => d,
            Err(fail) => return Ok(Err(fail)),
        };
        if dec.outputs != 1 {
            return Ok(Err(format!(
                "gate codomain carries {} output wires against exactly one",
                dec.outputs
            )));
        }
        let (is_bool, is_rat) = dec.out_kinds[0];
        if is_bool {
            return Err(
                "Boolean scalar gate codomain — the sign-fiber vs {0,\u{221E}}-face \
                 reading is not this leg's to decide; refusing over guessing"
                    .into(),
            );
        }
        if !is_rat {
            return Ok(Err("gate codomain is not a rational scalar wire".into()));
        }
        Ok(Ok(()))
    }
}
