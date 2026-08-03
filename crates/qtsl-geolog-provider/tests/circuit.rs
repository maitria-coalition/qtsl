//! The store-seam circuit family exercised end to end through
//! provider dispatch: `qtsl_kcite_wf`,
//! `qtsl_gate_scalar`, and the kernel-citation circuit arms of
//! `qtsl_tr_grain`/`qtsl_tr_endo` — real canonical store bytes built
//! with `maitria_hypernet::HypernetBuilder`, digests recomputed by
//! the codec itself, served through an in-memory [`MemStore`].
//!
//! The battery keeps the decode branch and the digest branch DISTINCT
//! (the topo-swap lesson): `store_truncated` is the guaranteed
//! decoder-branch specimen; `wrong_net_under_cited_digest` decodes
//! fine and dies at the digest recompute. Every decided-false mutant
//! is receipt-checked against the provider's named-violations
//! register ([`QtslGroundProvider::take_violations`], design memo
//! F-4), so each kill names its gate.
//!
//! The P/T fragment's regression witness is twofold: the whole
//! `tests/trwf.rs` suite runs untouched, and `pt_fragment_rides_the
//! _old_walk` here pins that a transition WITHOUT a `tr_kernel` row
//! reaches the landed marked-population walk (its distinctive
//! `mech_bag_base` refusal), never the circuit arm.

mod common;

use std::sync::Arc;

use common::{
    qtslcirc, qtslguard, qtslsys, qtsltr, sweep_indices, QTSLCIRC, QTSLGUARD, QTSLSYS, QTSLTR, REV,
};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use geolog_ground_api::Verdict;
use maitria_hypernet::{ConstPayload, Hypernet, HypernetBuilder, TensorType, WitRat};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use qtsl_geolog_provider::{MemStore, QtslGroundProvider, QtslVocab};

const OWN: [u8; 32] = [0x6D; 32];

// ---------------------------------------------------------------------
// Store fixtures: real canonical hypernets
// ---------------------------------------------------------------------

fn rat_scalar_const(b: &mut HypernetBuilder, n: i64) -> maitria_hypernet::Wire {
    b.constant(
        TensorType::rat([]),
        ConstPayload::Rat(vec![WitRat::from_i64(n, 1)]),
    )
    .expect("rat scalar const")
}

fn bool_scalar_const(b: &mut HypernetBuilder, v: bool) -> maitria_hypernet::Wire {
    b.constant(TensorType::boolean([]), ConstPayload::Bits(vec![v]))
        .expect("bool scalar const")
}

/// The control kernel net: 3 rational scalar inputs (state width 2 +
/// one noise draw), outputs = 3 Boolean scalar tags (positions 0–2)
/// + 2 rational scalar payload wires (positions 3–4).
fn kernel_net() -> Hypernet {
    let mut b = HypernetBuilder::new();
    for _ in 0..3 {
        b.input(TensorType::rat([]));
    }
    let t0 = bool_scalar_const(&mut b, true);
    let t1 = bool_scalar_const(&mut b, false);
    let t2 = bool_scalar_const(&mut b, false);
    let p0 = rat_scalar_const(&mut b, 1);
    let p1 = rat_scalar_const(&mut b, 2);
    b.finish(vec![t0, t1, t2, p0, p1]).expect("control net")
}

/// A valid net with the WRONG output interface for a width-2 state:
/// 2 inputs, 3 tags + 3 payload outputs (endo's payload mutant).
fn wide_payload_net() -> Hypernet {
    let mut b = HypernetBuilder::new();
    for _ in 0..2 {
        b.input(TensorType::rat([]));
    }
    let t0 = bool_scalar_const(&mut b, true);
    let t1 = bool_scalar_const(&mut b, false);
    let t2 = bool_scalar_const(&mut b, false);
    let p0 = rat_scalar_const(&mut b, 1);
    let p1 = rat_scalar_const(&mut b, 2);
    let p2 = rat_scalar_const(&mut b, 3);
    b.finish(vec![t0, t1, t2, p0, p1, p2])
        .expect("wide-payload net")
}

/// The control gate: exactly one rational scalar output.
fn gate_net() -> Hypernet {
    let mut b = HypernetBuilder::new();
    let g = rat_scalar_const(&mut b, 7);
    b.finish(vec![g]).expect("gate net")
}

/// The two-output gate (codomain-arity mutant).
fn two_output_gate_net() -> Hypernet {
    let mut b = HypernetBuilder::new();
    let g0 = rat_scalar_const(&mut b, 7);
    let g1 = rat_scalar_const(&mut b, 8);
    b.finish(vec![g0, g1]).expect("two-output gate net")
}

/// The Boolean scalar gate (the unadjudicated-reading refusal case).
fn bool_gate_net() -> Hypernet {
    let mut b = HypernetBuilder::new();
    let g = bool_scalar_const(&mut b, true);
    b.finish(vec![g]).expect("bool gate net")
}

fn hex_of(h: &Hypernet) -> String {
    h.digest().expect("digest").to_hex()
}

fn bytes_of(h: &Hypernet) -> Vec<u8> {
    h.canonical_bytes().expect("canonical bytes")
}

/// The standard store: every fixture net under its own digest.
fn full_store() -> MemStore {
    let mut s = MemStore::new();
    for net in [
        kernel_net(),
        wide_payload_net(),
        gate_net(),
        two_output_gate_net(),
        bool_gate_net(),
    ] {
        s.insert(hex_of(&net), bytes_of(&net));
    }
    s
}

// ---------------------------------------------------------------------
// Providers (per-test: the violations register is per instance)
// ---------------------------------------------------------------------

fn store_provider(store: MemStore) -> QtslGroundProvider {
    let vocab = QtslVocab::build(&sweep_indices());
    assert!(
        vocab.circuit.is_some() && vocab.gatescalar.is_some(),
        "circuit + gate-scalar vocabularies resolve: {:?}",
        vocab.notes
    );
    QtslGroundProvider::with_store(vec![REV], vocab, Arc::new(store))
}

fn storeless_provider() -> QtslGroundProvider {
    QtslGroundProvider::new(vec![REV], QtslVocab::build(&sweep_indices()))
}

fn ev_on(
    p: &QtslGroundProvider,
    name: &str,
    elems: &[u32],
    rows: &CertRows,
) -> Result<bool, String> {
    let local = p
        .local_by_name(name)
        .unwrap_or_else(|| panic!("`{name}` claimed"));
    let vals: Vec<Value> = elems
        .iter()
        .map(|e| Value::Ref(ElemRef::Local(*e)))
        .collect();
    let cells: Vec<Vec<u8>> = vals
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

// ---------------------------------------------------------------------
// Row fixtures (the test-side emitter shares no code with the
// evaluator's decoder)
// ---------------------------------------------------------------------

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
            deps: vec![QTSLSYS, QTSLTR, QTSLGUARD, QTSLCIRC],
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

    fn attr(&mut self, fun: Chid, subject: u32, value: Value) {
        self.ops.push(Op::Funa {
            fun: self.xref(fun),
            args: vec![lref(subject)],
            value,
        });
    }

    fn rela(&mut self, rel: Chid, args: Vec<Value>) {
        self.ops.push(Op::Rela {
            rel: self.xref(rel),
            args,
        });
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

/// Resolve a fun chid in the provider's own sweep order.
fn cfun(name: &str) -> Chid {
    qtslsys()
        .fun(name)
        .or_else(|| qtsltr().fun(name))
        .or_else(|| qtslguard().fun(name))
        .or_else(|| qtslcirc().fun(name))
        .unwrap_or_else(|| panic!("fun `{name}` in no swept index"))
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

fn strv(s: &str) -> Value {
    Value::Lit(Literal::str(s).expect("inline str"))
}

fn shapev(extents: &[u64]) -> Value {
    Value::Lit(Literal::shape(extents))
}

struct Builder {
    b: KitBody,
}

impl Builder {
    fn new() -> Builder {
        Builder { b: KitBody::new() }
    }

    /// A Box of closed intervals.
    fn image(&mut self, axes: &[(i64, i64)]) -> u32 {
        let mut cur = self.b.ctor(cfun("boxNil"), vec![]);
        for (lo, hi) in axes.iter().rev() {
            let iv = self
                .b
                .ctor(cfun("mkInterval"), vec![qv(*hi, 1), qv(*lo, 1)]);
            cur = self.b.ctor(cfun("boxCons"), vec![lref(iv), lref(cur)]);
        }
        cur
    }

    /// A `SysMech` system over a mechanism whose init box declares
    /// the state width; returns `(sys, mech)`.
    fn init_sys(&mut self, axes: &[(i64, i64)]) -> (u32, u32) {
        let mech = self.b.fresh();
        let bx = self.image(axes);
        // mech_init_box args bytewise: (box, mech).
        self.b
            .rela(cfun("mech_init_box"), vec![lref(bx), lref(mech)]);
        let sys = self.b.ctor(cfun("SysMech"), vec![lref(mech)]);
        (sys, mech)
    }

    /// A KernelCite over the digest `hex`, with an image box and the
    /// tag/noise roster data.
    #[allow(clippy::too_many_arguments)]
    fn kcite(
        &mut self,
        hex: &str,
        image_axes: &[(i64, i64)],
        next: u64,
        stay: u64,
        cemetery: u64,
        noise: &[u64],
    ) -> u32 {
        let hn = self.b.ctor(cfun("hnDigest"), vec![strv(hex)]);
        let image = self.image(image_axes);
        // mkKernelCite args bytewise: cemetery, hypernet, image,
        // next, noise, stay.
        self.b.ctor(
            cfun("mkKernelCite"),
            vec![
                natv(cemetery),
                lref(hn),
                lref(image),
                natv(next),
                shapev(noise),
                natv(stay),
            ],
        )
    }

    /// A kernel-citation transition: grWhole grain + a tr_kernel row.
    fn kernel_transition(&mut self, kc: u32) -> u32 {
        let tr = self.b.fresh();
        let grain = self.b.ctor(cfun("grWhole"), vec![]);
        self.b.attr(cfun("Transition/grain"), tr, lref(grain));
        // tr_kernel args bytewise: (kernel, tr).
        self.b.rela(cfun("tr_kernel"), vec![lref(kc), lref(tr)]);
        tr
    }

    /// A bare gate element: `hnDigest {sha256hex: hex}`.
    fn gate(&mut self, hex: &str) -> u32 {
        self.b.ctor(cfun("hnDigest"), vec![strv(hex)])
    }
}

/// The whole positive fixture: width-2 init box, control kernel net
/// cited with tags (0, 1, 2) and one noise draw at input 2; returns
/// `(builder, sys, kc, tr)`.
fn control_fixture() -> (Builder, u32, u32, u32) {
    let mut w = Builder::new();
    let (sys, _mech) = w.init_sys(&[(0, 1), (0, 1)]);
    let kc = w.kcite(&hex_of(&kernel_net()), &[(0, 1), (0, 1)], 0, 1, 2, &[2]);
    let tr = w.kernel_transition(kc);
    (w, sys, kc, tr)
}

// ---------------------------------------------------------------------
// Acceptance: the control fixture holds on all four store-seam walks
// ---------------------------------------------------------------------

#[test]
fn control_holds_everywhere() {
    let p = store_provider(full_store());
    let (mut w, sys, kc, tr) = control_fixture();
    let gate = w.gate(&hex_of(&gate_net()));
    let rows = w.b.rows();
    assert_eq!(ev_on(&p, "qtsl_kcite_wf", &[kc], &rows), Ok(true));
    assert_eq!(ev_on(&p, "qtsl_tr_grain", &[sys, tr], &rows), Ok(true));
    assert_eq!(ev_on(&p, "qtsl_tr_endo", &[sys, tr], &rows), Ok(true));
    assert_eq!(ev_on(&p, "qtsl_gate_scalar", &[gate], &rows), Ok(true));
    assert!(
        p.take_violations().is_empty(),
        "no decided-false on the control fixture"
    );
}

// ---------------------------------------------------------------------
// The committed mutant battery (each kill at a NAMED gate, receipts
// through the violations register)
// ---------------------------------------------------------------------

#[test]
fn truncated_store_bytes_die_at_the_decode_branch() {
    // THE decoder-branch specimen (kept distinct from the digest
    // branch — the inc-2 topo-swap lesson).
    let mut bytes = bytes_of(&kernel_net());
    bytes.truncate(bytes.len() - 3);
    let mut s = MemStore::new();
    s.insert(hex_of(&kernel_net()), bytes);
    let p = store_provider(s);
    let (w, _sys, kc, _tr) = control_fixture();
    let rows = w.b.rows();
    assert_eq!(ev_on(&p, "qtsl_kcite_wf", &[kc], &rows), Ok(false));
    let v = p.take_violations();
    assert_eq!(v.len(), 1, "one decided-false, one register line: {v:?}");
    assert!(
        v[0].starts_with("qtsl_kcite_wf:") && v[0].contains("does not decode canonically"),
        "the decode branch is the named gate: {v:?}"
    );
}

#[test]
fn wrong_net_under_the_cited_digest_dies_at_the_digest_branch() {
    // A DIFFERENT valid hypernet bound under the cited digest:
    // decodes fine, the recompute disagrees.
    let mut s = MemStore::new();
    s.insert(hex_of(&kernel_net()), bytes_of(&gate_net()));
    let p = store_provider(s);
    let (w, _sys, kc, _tr) = control_fixture();
    let rows = w.b.rows();
    assert_eq!(ev_on(&p, "qtsl_kcite_wf", &[kc], &rows), Ok(false));
    let v = p.take_violations();
    assert!(
        v.len() == 1 && v[0].starts_with("qtsl_kcite_wf:") && v[0].contains("digest recompute"),
        "the digest branch is the named gate: {v:?}"
    );
    assert!(
        p.take_violations().is_empty(),
        "the register drains: a second take is empty"
    );
}

#[test]
fn grain_input_width_mismatch_fails() {
    // An empty noise roster against the 3-input control net: the
    // state block explains only 2 inputs.
    let p = store_provider(full_store());
    let mut w = Builder::new();
    let (sys, _mech) = w.init_sys(&[(0, 1), (0, 1)]);
    let kc = w.kcite(&hex_of(&kernel_net()), &[(0, 1), (0, 1)], 0, 1, 2, &[]);
    let tr = w.kernel_transition(kc);
    let rows = w.b.rows();
    // The citation itself stays well-formed (noise is vacuously
    // ascending) — only the grain tie fails.
    assert_eq!(ev_on(&p, "qtsl_kcite_wf", &[kc], &rows), Ok(true));
    assert_eq!(ev_on(&p, "qtsl_tr_grain", &[sys, tr], &rows), Ok(false));
    let v = p.take_violations();
    assert!(
        v.len() == 1 && v[0].starts_with("qtsl_tr_grain:") && v[0].contains("kernel input arity"),
        "the input-arity tie is the named gate: {v:?}"
    );
}

#[test]
fn endo_payload_width_mismatch_fails() {
    // The wide-payload net (3 tags + 3 payload) against a width-2
    // state block.
    let p = store_provider(full_store());
    let mut w = Builder::new();
    let (sys, _mech) = w.init_sys(&[(0, 1), (0, 1)]);
    let kc = w.kcite(
        &hex_of(&wide_payload_net()),
        &[(0, 1), (0, 1)],
        0,
        1,
        2,
        &[],
    );
    let tr = w.kernel_transition(kc);
    let rows = w.b.rows();
    assert_eq!(ev_on(&p, "qtsl_tr_endo", &[sys, tr], &rows), Ok(false));
    let v = p.take_violations();
    assert!(
        v.len() == 1 && v[0].starts_with("qtsl_tr_endo:") && v[0].contains("kernel payload"),
        "the payload tie is the named gate: {v:?}"
    );
}

#[test]
fn endo_enclosure_count_mismatch_fails() {
    // A one-interval landing enclosure against a width-2 state block
    // (the citation stays well-formed: interval order + floor hold).
    let p = store_provider(full_store());
    let mut w = Builder::new();
    let (sys, _mech) = w.init_sys(&[(0, 1), (0, 1)]);
    let kc = w.kcite(&hex_of(&kernel_net()), &[(0, 1)], 0, 1, 2, &[2]);
    let tr = w.kernel_transition(kc);
    let rows = w.b.rows();
    assert_eq!(ev_on(&p, "qtsl_kcite_wf", &[kc], &rows), Ok(true));
    assert_eq!(ev_on(&p, "qtsl_tr_endo", &[sys, tr], &rows), Ok(false));
    let v = p.take_violations();
    assert!(
        v.iter()
            .any(|l| l.starts_with("qtsl_tr_endo:") && l.contains("landing enclosure")),
        "the enclosure-count tie is the named gate: {v:?}"
    );
}

#[test]
fn two_output_gate_fails() {
    let p = store_provider(full_store());
    let mut w = Builder::new();
    let gate = w.gate(&hex_of(&two_output_gate_net()));
    let rows = w.b.rows();
    assert_eq!(ev_on(&p, "qtsl_gate_scalar", &[gate], &rows), Ok(false));
    let v = p.take_violations();
    assert!(
        v.len() == 1
            && v[0].starts_with("qtsl_gate_scalar:")
            && v[0].contains("against exactly one"),
        "the codomain-arity demand is the named gate: {v:?}"
    );
}

#[test]
fn bool_scalar_gate_refuses() {
    // The sign-fiber vs {0,∞}-face reading is not this leg's to
    // decide (design memo adjudication): refusal, never a verdict.
    let p = store_provider(full_store());
    let mut w = Builder::new();
    let gate = w.gate(&hex_of(&bool_gate_net()));
    let rows = w.b.rows();
    let err = ev_on(&p, "qtsl_gate_scalar", &[gate], &rows).unwrap_err();
    assert!(
        err.contains("Boolean scalar gate codomain"),
        "the Bool codomain refuses with the case named: {err}"
    );
    assert!(
        p.take_violations().is_empty(),
        "a refusal never feeds the violations register"
    );
}

#[test]
fn absent_digest_refuses() {
    // An empty store: the cited content is unreachable — refusal,
    // never a guessed verdict.
    let p = store_provider(MemStore::new());
    let (w, _sys, kc, _tr) = control_fixture();
    let rows = w.b.rows();
    let err = ev_on(&p, "qtsl_kcite_wf", &[kc], &rows).unwrap_err();
    assert!(
        err.contains("unreachable") && err.contains("refusing over guessing"),
        "the absent object refuses with the case named: {err}"
    );
}

#[test]
fn storeless_provider_refuses_with_the_case_named() {
    // A plain `new()` provider still CLAIMS the store-seam relations
    // (vocabulary-gated, never store-gated) and refuses per instance.
    let p = storeless_provider();
    let (mut w, sys, kc, tr) = control_fixture();
    let gate = w.gate(&hex_of(&gate_net()));
    let rows = w.b.rows();
    for (rel, elems) in [
        ("qtsl_kcite_wf", vec![kc]),
        ("qtsl_tr_grain", vec![sys, tr]),
        ("qtsl_tr_endo", vec![sys, tr]),
        ("qtsl_gate_scalar", vec![gate]),
    ] {
        let err = ev_on(&p, rel, &elems, &rows).unwrap_err();
        assert!(
            err.contains("no store attached"),
            "`{rel}` refuses storeless with the case named: {err}"
        );
    }
}

// ---------------------------------------------------------------------
// Fragment routing
// ---------------------------------------------------------------------

#[test]
fn pt_fragment_rides_the_old_walk() {
    // No tr_kernel row: grain/endo route to the landed P/T walk —
    // whose distinctive refusal on this fixture (a mechanism with an
    // init box but no bag rows) names mech_bag_base, a demand the
    // circuit arm never states.
    let p = store_provider(full_store());
    let mut w = Builder::new();
    let (sys, _mech) = w.init_sys(&[(0, 1), (0, 1)]);
    let tr = w.b.fresh();
    let grain = w.b.ctor(cfun("grWhole"), vec![]);
    w.b.attr(cfun("Transition/grain"), tr, lref(grain));
    let rows = w.b.rows();
    for rel in ["qtsl_tr_grain", "qtsl_tr_endo"] {
        let err = ev_on(&p, rel, &[sys, tr], &rows).unwrap_err();
        assert!(
            err.contains("mech_bag_base"),
            "`{rel}` without a tr_kernel row rides the P/T walk: {err}"
        );
    }
}

#[test]
fn non_whole_grain_refuses_the_circuit_arm() {
    // A kernel-citation transition whose grain is grTuple: the
    // circuit fragment is grWhole-only — refusal with the case named
    // (the driver walk's own gate, ported).
    let p = store_provider(full_store());
    let mut w = Builder::new();
    let (sys, _mech) = w.init_sys(&[(0, 1), (0, 1)]);
    let kc = w.kcite(&hex_of(&kernel_net()), &[(0, 1), (0, 1)], 0, 1, 2, &[2]);
    let tr = w.b.fresh();
    let ssl = w.b.ctor(cfun("sslNil"), vec![]);
    let grain = w.b.ctor(cfun("grTuple"), vec![lref(ssl)]);
    w.b.attr(cfun("Transition/grain"), tr, lref(grain));
    w.b.rela(cfun("tr_kernel"), vec![lref(kc), lref(tr)]);
    let rows = w.b.rows();
    let err = ev_on(&p, "qtsl_tr_grain", &[sys, tr], &rows).unwrap_err();
    assert!(
        err.contains("grain is not grWhole"),
        "the circuit grain arm refuses non-whole grains: {err}"
    );
}

// ---------------------------------------------------------------------
// The violations register (design memo F-4)
// ---------------------------------------------------------------------

#[test]
fn violations_register_names_and_drains() {
    // Three decided-false walks on one provider: three register
    // lines, each `<relation>: <why>`; a second drain is empty.
    let mut s = MemStore::new();
    s.insert(hex_of(&kernel_net()), bytes_of(&gate_net())); // digest mutant
    s.insert(
        hex_of(&two_output_gate_net()),
        bytes_of(&two_output_gate_net()),
    );
    let p = store_provider(s);
    let (mut w, sys, kc, tr) = control_fixture();
    let gate = w.gate(&hex_of(&two_output_gate_net()));
    let rows = w.b.rows();
    assert_eq!(ev_on(&p, "qtsl_kcite_wf", &[kc], &rows), Ok(false));
    assert_eq!(ev_on(&p, "qtsl_tr_grain", &[sys, tr], &rows), Ok(false));
    assert_eq!(ev_on(&p, "qtsl_gate_scalar", &[gate], &rows), Ok(false));
    let v = p.take_violations();
    assert_eq!(v.len(), 3, "one line per decided-false: {v:?}");
    assert!(v[0].starts_with("qtsl_kcite_wf: "), "{v:?}");
    assert!(v[1].starts_with("qtsl_tr_grain: "), "{v:?}");
    assert!(v[2].starts_with("qtsl_gate_scalar: "), "{v:?}");
    assert!(p.take_violations().is_empty(), "the register drains");
}

// ---------------------------------------------------------------------
// Roster
// ---------------------------------------------------------------------

#[test]
fn provider_claims_the_family() {
    let p = common::provider();
    for name in ["qtsl_kcite_wf", "qtsl_gate_scalar"] {
        assert!(p.local_by_name(name).is_some(), "`{name}` claimed");
    }
}
