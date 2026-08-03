//! The dwell-gate walk exercised end to end through provider dispatch:
//! `qtsl_dwell_gate` — real canonical store bytes built
//! with `maitria_hypernet::HypernetBuilder`, digests recomputed by
//! the codec itself, served through an in-memory `MemStore`.
//!
//! The committed battery is the design memo's D-6 roster: control C1
//! (fiber = window exactly) plus mutants M-1…M-10, each killed at a
//! NAMED gate, receipts through the violations register. The decode
//! branch (M-4, truncation) and the digest branch (M-10, wrong net
//! under the cited digest) stay DISTINCT specimens — the topo-swap
//! lesson, carried through the circuit battery.

mod common;

use std::sync::Arc;

use common::{
    qtslcirc, qtslguard, qtslsys, qtsltr, sweep_indices, QTSLCIRC, QTSLGUARD, QTSLSYS, QTSLTR, REV,
};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use geolog_ground_api::Verdict;
use maitria_hypernet::{ConstPayload, Hypernet, HypernetBuilder, SimpC, TensorType, Wire, WitRat};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use qtsl_geolog_provider::{MemStore, QtslGroundProvider, QtslVocab};

const OWN: [u8; 32] = [0x6E; 32];

// ---------------------------------------------------------------------
// Store fixtures: real canonical gate nets
// ---------------------------------------------------------------------

fn wr(n: i64, d: i64) -> WitRat {
    WitRat::from_i64(n, d)
}

/// A univariate polynomial gate `p(t) = Σ coeffs[k]·t^k` over one
/// rational scalar duration input, assembled from the ten-box
/// vocabulary: `copy` fans the input out, `contract` with no index
/// variables multiplies scalars, `stack` + a ones-`contract` sums the
/// terms (the tenth box's sum idiom).
fn poly_gate(coeffs: &[(i64, i64)]) -> Hypernet {
    let mut b = HypernetBuilder::new();
    let t = b.input(TensorType::rat([]));
    // t-power wires needed: k copies per degree-k term with a nonzero
    // coefficient.
    let need: Vec<(usize, (i64, i64))> = coeffs
        .iter()
        .enumerate()
        .filter(|(k, (n, _))| *k > 0 && *n != 0)
        .map(|(k, c)| (k, *c))
        .collect();
    let total: usize = need.iter().map(|(k, _)| k).sum();
    let mut t_wires: Vec<Wire> = if total == 0 {
        Vec::new()
    } else if total == 1 {
        vec![t]
    } else {
        b.copy(t, total as u32).expect("copy the duration wire")
    };
    let mut terms: Vec<Wire> = Vec::new();
    // The constant term (always present, so a pure-constant gate still
    // has a term to sum).
    let c0 = coeffs.first().copied().unwrap_or((0, 1));
    terms.push(
        b.constant(TensorType::rat([]), ConstPayload::Rat(vec![wr(c0.0, c0.1)]))
            .expect("constant term"),
    );
    for (k, (n, d)) in need {
        let pow_wires: Vec<Wire> = t_wires.drain(..k).collect();
        let tk = if k == 1 {
            pow_wires[0]
        } else {
            b.contract(&pow_wires, &[], &vec![vec![]; k], &[])
                .expect("scalar power contract")
        };
        let ck = b
            .constant(TensorType::rat([]), ConstPayload::Rat(vec![wr(n, d)]))
            .expect("coefficient");
        let term = b
            .contract(&[tk, ck], &[], &[vec![], vec![]], &[])
            .expect("scalar term contract");
        terms.push(term);
    }
    let stacked = b.stack(&terms).expect("stack the terms");
    let n = terms.len() as u64;
    let ones = b
        .constant(
            TensorType::rat([n]),
            ConstPayload::Rat(vec![wr(1, 1); n as usize]),
        )
        .expect("ones");
    let sum = b
        .contract(&[stacked, ones], &[n], &[vec![0], vec![0]], &[])
        .expect("sum contract");
    b.finish(vec![sum]).expect("gate net")
}

/// The C1 control on the window [1, 3]: `p(t) = (t−1)(3−t)`
/// = −t² + 4t − 3, fiber exactly [1, 3].
fn c1_gate() -> Hypernet {
    poly_gate(&[(-3, 1), (4, 1), (-1, 1)])
}

/// M-1: `p(t) = t − 1` — fiber [1, ∞), leaking past a finite ceiling.
fn leak_right_gate() -> Hypernet {
    poly_gate(&[(-1, 1), (1, 1)])
}

/// M-2: `p(t) = 3 − t` — fiber (−∞, 3], leaking left of the floor.
fn leak_left_gate() -> Hypernet {
    poly_gate(&[(3, 1), (-1, 1)])
}

/// M-3: `p ≡ −1` — dead on every window.
fn dead_gate() -> Hypernet {
    poly_gate(&[(-1, 1)])
}

/// M-5: `p(t) = (t−2)(3−t)` = −t² + 5t − 6 — fiber [2, 3], zero
/// exactly at the ceiling, otherwise interior to [1, 3].
fn boundary_touch_gate() -> Hypernet {
    poly_gate(&[(-6, 1), (5, 1), (-1, 1)])
}

/// M-6: a Cell-bearing gate — scalar rational interface (the shape
/// gates pass), one `cell` application inside (the fragment pin
/// refuses by name). Complex: the segment [0, 1] in ambient
/// dimension 1, one cell.
fn cell_gate() -> Hypernet {
    let mut b = HypernetBuilder::new();
    let t = b.input(TensorType::rat([]));
    let seg = SimpC::new(
        1,
        vec![vec![wr(0, 1)], vec![wr(1, 1)]],
        vec![
            [0u32].into_iter().collect(),
            [1u32].into_iter().collect(),
            [0u32, 1].into_iter().collect(),
        ],
        vec![([0u32, 1].into_iter().collect(), Default::default())],
    );
    let cx = b.add_complex(seg).expect("valid segment complex");
    let t1 = b.reshape(t, &[1]).expect("reshape to the ambient dim");
    let outs = b.cell(cx, t1).expect("cell");
    for o in outs {
        b.delete(o).expect("discard the membership bits");
    }
    let g = b
        .constant(TensorType::rat([]), ConstPayload::Rat(vec![wr(1, 1)]))
        .expect("output const");
    b.finish(vec![g]).expect("cell gate net")
}

/// M-9: a 2-input net with a rational scalar output — not a unary
/// duration gate.
fn two_input_gate() -> Hypernet {
    let mut b = HypernetBuilder::new();
    b.input(TensorType::rat([]));
    b.input(TensorType::rat([]));
    let g = b
        .constant(TensorType::rat([]), ConstPayload::Rat(vec![wr(1, 1)]))
        .expect("output const");
    b.finish(vec![g]).expect("two-input net")
}

fn hex_of(h: &Hypernet) -> String {
    h.digest().expect("digest").to_hex()
}

fn bytes_of(h: &Hypernet) -> Vec<u8> {
    h.canonical_bytes().expect("canonical bytes")
}

fn full_store() -> MemStore {
    let mut s = MemStore::new();
    for net in [
        c1_gate(),
        leak_right_gate(),
        leak_left_gate(),
        dead_gate(),
        boundary_touch_gate(),
        cell_gate(),
        two_input_gate(),
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
        vocab.dwellgate.is_some(),
        "dwell-gate vocabulary resolves: {:?}",
        vocab.notes
    );
    QtslGroundProvider::with_store(vec![REV], vocab, Arc::new(store))
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

    fn ctor(&mut self, fun: &str, args: Vec<Value>) -> u32 {
        let e = self.fresh();
        self.ops.push(Op::Funa {
            fun: self.xref(cfun(fun)),
            args,
            value: Value::Ref(ElemRef::Local(e)),
        });
        e
    }

    fn attr(&mut self, fun: &str, subject: u32, value: Value) {
        self.ops.push(Op::Funa {
            fun: self.xref(cfun(fun)),
            args: vec![lref(subject)],
            value,
        });
    }

    fn rela(&mut self, rel: &str, args: Vec<Value>) {
        self.ops.push(Op::Rela {
            rel: self.xref(cfun(rel)),
            args,
        });
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

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

fn strv(s: &str) -> Value {
    Value::Lit(Literal::str(s).expect("inline str"))
}

/// A carved-window transition with a gate row: clock =
/// `tkCarved {floor, ceil}` (finite ceiling), gate = `hnDigest {hex}`.
/// Returns `(kit, tr)`.
fn carved_fixture(hex: &str, floor: (i64, u64), ceil: Option<(i64, u64)>) -> (KitBody, u32) {
    let mut w = KitBody::new();
    let tr = w.fresh();
    let en = match ceil {
        Some((n, d)) => w.ctor("enFin", vec![qv(n, d)]),
        None => w.ctor("enInf", vec![]),
    };
    // tkCarved args bytewise: (ceil, floor).
    let clock = w.ctor("tkCarved", vec![lref(en), qv(floor.0, floor.1)]);
    w.attr("Transition/clock", tr, lref(clock));
    let gate = w.ctor("hnDigest", vec![strv(hex)]);
    // tr_dwell_gate args bytewise: (gate, tr).
    w.rela("tr_dwell_gate", vec![lref(gate), lref(tr)]);
    (w, tr)
}

fn assert_fails_named(store: MemStore, kit: &KitBody, tr: u32, gate_fragment: &str) {
    let p = store_provider(store);
    let rows = kit.rows();
    assert_eq!(ev_on(&p, "qtsl_dwell_gate", &[tr], &rows), Ok(false));
    let v = p.take_violations();
    assert_eq!(v.len(), 1, "one decided-false, one register line: {v:?}");
    assert!(
        v[0].starts_with("qtsl_dwell_gate:") && v[0].contains(gate_fragment),
        "the named gate is `{gate_fragment}`: {v:?}"
    );
}

fn assert_refuses_named(store: MemStore, kit: &KitBody, tr: u32, reason_fragment: &str) {
    let p = store_provider(store);
    let rows = kit.rows();
    match ev_on(&p, "qtsl_dwell_gate", &[tr], &rows) {
        Err(why) => assert!(
            why.contains(reason_fragment),
            "refusal names `{reason_fragment}`: {why}"
        ),
        other => panic!("expected a refusal, got {other:?}"),
    }
    assert!(
        p.take_violations().is_empty(),
        "refusals never touch the register"
    );
}

// ---------------------------------------------------------------------
// C1 — the control: fiber = window exactly
// ---------------------------------------------------------------------

#[test]
fn c1_fiber_equals_window_holds() {
    let (kit, tr) = carved_fixture(&hex_of(&c1_gate()), (1, 1), Some((3, 1)));
    let p = store_provider(full_store());
    let rows = kit.rows();
    assert_eq!(ev_on(&p, "qtsl_dwell_gate", &[tr], &rows), Ok(true));
    assert!(
        p.take_violations().is_empty(),
        "no register lines on the control"
    );
}

/// The same control gate on an INFINITE window [1, ∞): the fiber
/// [1, 3] sits inside it and the floor witnesses — Holds (the enInf
/// leg of the walk, exercised on the control shape).
#[test]
fn c1_gate_on_infinite_window_holds() {
    let (kit, tr) = carved_fixture(&hex_of(&c1_gate()), (1, 1), None);
    let p = store_provider(full_store());
    let rows = kit.rows();
    assert_eq!(ev_on(&p, "qtsl_dwell_gate", &[tr], &rows), Ok(true));
    assert!(p.take_violations().is_empty());
}

// ---------------------------------------------------------------------
// The committed mutant battery (M-1…M-10)
// ---------------------------------------------------------------------

/// M-1 — fiber-leak right: the gate stays nonnegative past a finite
/// ceiling; the containment witness (never the Bernstein enclosure)
/// names the point.
#[test]
fn m1_fiber_leak_right_fails_with_witness() {
    let (kit, tr) = carved_fixture(&hex_of(&leak_right_gate()), (1, 1), Some((3, 1)));
    assert_fails_named(full_store(), &kit, tr, "> ceil");
}

/// M-2 — fiber-leak left of the floor.
#[test]
fn m2_fiber_leak_left_fails_with_witness() {
    let (kit, tr) = carved_fixture(&hex_of(&leak_left_gate()), (1, 1), Some((3, 1)));
    assert_fails_named(full_store(), &kit, tr, "< floor");
}

/// M-3 — dead gate: negative on the whole window; dies at the
/// emptiness certificate.
#[test]
fn m3_dead_gate_fails_at_the_emptiness_certificate() {
    let (kit, tr) = carved_fixture(&hex_of(&dead_gate()), (1, 1), Some((3, 1)));
    assert_fails_named(full_store(), &kit, tr, "gate dead on its window");
}

/// M-4 — store truncation: THE decoder-branch specimen (distinct
/// from the digest branch, the inc-2 topo-swap lesson).
#[test]
fn m4_truncated_store_bytes_die_at_the_decode_branch() {
    let mut bytes = bytes_of(&c1_gate());
    bytes.truncate(bytes.len() - 3);
    let mut s = MemStore::new();
    s.insert(hex_of(&c1_gate()), bytes);
    let (kit, tr) = carved_fixture(&hex_of(&c1_gate()), (1, 1), Some((3, 1)));
    assert_fails_named(s, &kit, tr, "does not decode canonically");
}

/// M-5 — boundary touch: gate zero exactly at the ceiling, fiber
/// otherwise interior. Holds under the nonneg sign-fiber reading
/// (design memo D-1's pin; the tail certificates cover both
/// readings).
#[test]
fn m5_boundary_touch_holds() {
    let (kit, tr) = carved_fixture(&hex_of(&boundary_touch_gate()), (1, 1), Some((3, 1)));
    let p = store_provider(full_store());
    let rows = kit.rows();
    assert_eq!(ev_on(&p, "qtsl_dwell_gate", &[tr], &rows), Ok(true));
    assert!(p.take_violations().is_empty());
}

/// M-6 — Cell-bearing gate: the fragment pin refuses BY NAME (the
/// refusal register asserts the "Cell box" string; the theory's own
/// presenter stratum is cell-free).
#[test]
fn m6_cell_bearing_gate_refuses_the_fragment() {
    let (kit, tr) = carved_fixture(&hex_of(&cell_gate()), (1, 1), Some((3, 1)));
    assert_refuses_named(full_store(), &kit, tr, "Cell box");
}

/// M-7 — two distinct gate rows: at-most-one is admission
/// conformance, not this walk's to adjudicate.
#[test]
fn m7_two_gate_rows_refuse() {
    let (mut kit, tr) = carved_fixture(&hex_of(&c1_gate()), (1, 1), Some((3, 1)));
    let g2 = kit.ctor("hnDigest", vec![strv(&hex_of(&dead_gate()))]);
    kit.rela("tr_dwell_gate", vec![lref(g2), lref(tr)]);
    assert_refuses_named(full_store(), &kit, tr, "multiple distinct gate rows");
}

/// M-8 — wrong-wing clock: a gate row on tkRace (chase-refused
/// upstream; named here for storeless/partial-DB runs).
#[test]
fn m8_wrong_wing_clock_refuses() {
    let mut w = KitBody::new();
    let tr = w.fresh();
    let en = w.ctor("enFin", vec![qv(1, 1)]);
    let clock = w.ctor("tkRace", vec![lref(en)]);
    w.attr("Transition/clock", tr, lref(clock));
    let gate = w.ctor("hnDigest", vec![strv(&hex_of(&c1_gate()))]);
    w.rela("tr_dwell_gate", vec![lref(gate), lref(tr)]);
    assert_refuses_named(full_store(), &w, tr, "non-carved clock wing");
}

/// M-9 — a 2-input net is definitively not a duration carve: decided
/// FALSE (the vocabulary determines the reading).
#[test]
fn m9_two_input_net_fails_the_shape_gate() {
    let (kit, tr) = carved_fixture(&hex_of(&two_input_gate()), (1, 1), Some((3, 1)));
    assert_fails_named(full_store(), &kit, tr, "not a unary duration gate");
}

/// M-10 — digest lie: a DIFFERENT valid net bound under the cited
/// digest — decodes fine, dies at the digest recompute (distinct
/// from M-4's decode branch).
#[test]
fn m10_digest_lie_dies_at_the_digest_branch() {
    let mut s = MemStore::new();
    s.insert(hex_of(&c1_gate()), bytes_of(&dead_gate()));
    let (kit, tr) = carved_fixture(&hex_of(&c1_gate()), (1, 1), Some((3, 1)));
    assert_fails_named(s, &kit, tr, "digest recompute");
}

/// The register drains: a second take after a decided-false is empty.
#[test]
fn register_drains_between_takes() {
    let (kit, tr) = carved_fixture(&hex_of(&dead_gate()), (1, 1), Some((3, 1)));
    let p = store_provider(full_store());
    let rows = kit.rows();
    assert_eq!(ev_on(&p, "qtsl_dwell_gate", &[tr], &rows), Ok(false));
    assert_eq!(p.take_violations().len(), 1);
    assert!(p.take_violations().is_empty());
}
