//! The upper-coverage CLOSED-membership compat guard, exercised
//! against the third footprint polarity (`hrpDropAtMost`, the
//! revision-event-7 carve): **`qtsl_hplate_coverage` counts exactly
//! rows of polarity `hrpSafety` or `hrpGap`** — a dropAtMost row
//! bounds nothing above and never covers, and an evaluator that
//! counted one toward upper coverage would silently unsound the
//! landed FromFold nodes (their soundness argument reads "every
//! may-touch transition carries an UPPER row", and a drop-by-at-most
//! sequent is no upper bound).
//!
//! Vocabulary: the baked qc index EXTENDED in-test with the
//! dropAtMost declarations (the nullary polarity + the ℚ `ubound`
//! attribute), cloned from their landed siblings at fresh counters —
//! modeling exactly what the revision event's declarations add. The
//! guard keys on CLOSED membership {safety, gap}, so its code path is
//! identical for the minted polarity and any future non-upper member;
//! the mint's own battery re-run exercises the name-resolution face.
//!
//! The pair idiom must SURVIVE the guard: `{hrpSafety,
//! hrpDropAtMost(0)}` (exact conservation) and `{hrpGap(g),
//! hrpDropAtMost(g)}` (displacement exactly −g) put both halves on
//! one (cert, transition) — the guard filters non-upper rows out of
//! the covering count, it never refuses their presence.
//!
//! The footprint SEQUENT on a dropAtMost row refuses loudly: its
//! swapped-sides semantics (produced ≥ consumed − u) is a named
//! successor of the sequent evaluator — deciding TRUE would be
//! unsound, deciding FALSE would mis-decide a sequent that may hold.

use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use geolog_ground_api::Verdict;
use qtsl_geolog_provider::reprovocab::baked::{
    baked_vocab_from_container, qc_v1_container_bytes, BAKED_QC_V1_REV,
};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::TheoryIndex;
use qtsl_geolog_provider::{QtslGroundProvider, QtslVocab};

/// The baked qc index plus the two event-7 dropAtMost declarations,
/// cloned from their landed siblings (`hrpSafety`,
/// `HFootprintRow/gap`) at fresh counters — no shape is transcribed
/// by hand, so a loader change moves these clones with it.
fn extended_index() -> TheoryIndex {
    let vocab = baked_vocab_from_container(qc_v1_container_bytes(), BAKED_QC_V1_REV)
        .expect("qc chain derives");
    let mut idx = vocab.index.clone();
    let fresh = idx
        .funs
        .iter()
        .map(|d| d.chid.1)
        .chain(idx.sorts_by_chid.keys().map(|c| c.1))
        .max()
        .expect("nonempty index")
        + 1;
    let mut pol = idx
        .fun("hrpSafety")
        .expect("landed polarity declares")
        .clone();
    pol.name = "hrpDropAtMost".to_string();
    pol.chid = (BAKED_QC_V1_REV, fresh);
    idx.insert_fun(pol);
    let mut ub = idx
        .fun("HFootprintRow/gap")
        .expect("landed gap attribute declares")
        .clone();
    ub.name = "HFootprintRow/ubound".to_string();
    ub.chid = (BAKED_QC_V1_REV, fresh + 1);
    idx.insert_fun(ub);
    idx
}

fn setup() -> (TheoryIndex, QtslGroundProvider) {
    let idx = extended_index();
    let qv = QtslVocab::build(&[&idx]);
    assert!(
        qv.hplate.is_some(),
        "hplate family resolves over the extended index: {:?}",
        qv.notes
    );
    let provider = QtslGroundProvider::new(vec![[0x2f; 32]], qv);
    (idx, provider)
}

fn lref(n: u32) -> Value {
    Value::Ref(ElemRef::Local(n))
}
fn q(n: i64, d: u64) -> Value {
    Value::Lit(Literal::q(n, d).unwrap())
}
fn nat(n: u64) -> Value {
    Value::Lit(Literal::nat(n))
}
fn shape(extents: &[u64]) -> Value {
    Value::Lit(Literal::shape(extents))
}

/// Ops builder over the extended index (the `hplate_baked` harness,
/// re-homed onto a bare [`TheoryIndex`]).
struct Cx<'a> {
    idx: &'a TheoryIndex,
    ops: Vec<Op>,
    next: u32,
}

impl<'a> Cx<'a> {
    fn new(idx: &'a TheoryIndex) -> Cx<'a> {
        Cx {
            idx,
            ops: Vec::new(),
            next: 0,
        }
    }
    fn fun_ref(&self, name: &str) -> ElemRef {
        let d = self
            .idx
            .fun(name)
            .unwrap_or_else(|| panic!("index declares `{name}`"));
        assert_eq!(d.chid.0, BAKED_QC_V1_REV);
        ElemRef::External {
            dep_index: 0,
            counter: d.chid.1,
        }
    }
    fn sort_ref(&self, name: &str) -> ElemRef {
        let chid = self
            .idx
            .sort(name)
            .unwrap_or_else(|| panic!("index declares sort `{name}`"));
        assert_eq!(chid.0, BAKED_QC_V1_REV);
        ElemRef::External {
            dep_index: 0,
            counter: chid.1,
        }
    }
    fn elta(&mut self, sort: &str) -> u32 {
        self.ops.push(Op::Elta {
            sort: self.sort_ref(sort),
        });
        self.next += 1;
        self.next - 1
    }
    fn funa(&mut self, fun: &str, args: Vec<Value>, value: u32) {
        self.ops.push(Op::Funa {
            fun: self.fun_ref(fun),
            args,
            value: lref(value),
        });
    }
    fn attr(&mut self, fun: &str, subject: u32, value: Value) {
        self.ops.push(Op::Funa {
            fun: self.fun_ref(fun),
            args: vec![lref(subject)],
            value,
        });
    }
    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, [0xAB; 32], &[BAKED_QC_V1_REV])
    }
}

/// One footprint row on the drain transition, by polarity.
enum RowPol {
    Safety,
    /// gap g (numerator, denominator)
    Gap(i64, u64),
    /// ubound u (numerator, denominator)
    Drop(i64, u64),
}

struct Base {
    cert: u32,
    rows: Vec<u32>,
}

/// The minimal P/T drain of the landed hplate battery — one token
/// species at count 5, one draining transition (grWhole, Dirac reset
/// `x_0 − 1`), one plate with the constant-1 feature, a `hagSum`
/// certificate — with the footprint-row roster on the drain
/// transition given by `pols`. The drain transition is may-touch by
/// construction (the certificate cites a plate), so coverage turns
/// exactly on which of its rows COUNT.
fn build_drain(cx: &mut Cx, pols: &[RowPol]) -> Base {
    // Token base system (content-free).
    let mb = cx.elta("Mech");
    let sb = cx.elta("System");
    cx.funa("SysMech", vec![lref(mb)], sb);
    // Subject.
    let m = cx.elta("Mech");
    let sys = cx.elta("System");
    cx.funa("SysMech", vec![lref(m)], sys);
    cx.ops.push(Op::Rela {
        rel: cx.fun_ref("mech_bag_base"),
        args: vec![lref(sb), lref(m)],
    });
    let tk = cx.elta("Token");
    cx.ops.push(Op::Rela {
        rel: cx.fun_ref("mech_bag_marking"),
        args: vec![nat(5), lref(m), lref(tk)],
    });
    cx.ops.push(Op::Rela {
        rel: cx.fun_ref("mech_bag_wire"),
        args: vec![lref(m), lref(tk), nat(0)],
    });

    // The drain transition: grWhole grain, Dirac reset x_0 − 1.
    let tr = cx.elta("Transition");
    cx.ops.push(Op::Rela {
        rel: cx.fun_ref("sys_transition"),
        args: vec![lref(sys), lref(tr)],
    });
    let g = cx.elta("TrGrain");
    cx.funa("grWhole", vec![], g);
    cx.attr("Transition/grain", tr, lref(g));
    let pzero = cx.elta("Poly");
    cx.funa("pZero", vec![], pzero);
    let cm1 = cx.elta("Poly");
    cx.funa("pTerm", vec![q(-1, 1), shape(&[0]), lref(pzero)], cm1);
    let x0m1 = cx.elta("Poly");
    cx.funa("pTerm", vec![q(1, 1), shape(&[1]), lref(cm1)], x0m1);
    let pvnil = cx.elta("PolyVec");
    cx.funa("pvNil", vec![], pvnil);
    let pv = cx.elta("PolyVec");
    cx.funa("pvCons", vec![lref(x0m1), lref(pvnil)], pv);
    let image = cx.elta("Box");
    let step = cx.elta("StepRes");
    cx.funa("srNext", vec![lref(image), lref(pv)], step);
    let sbnil = cx.elta("StepBranchList");
    cx.funa("sbNil", vec![], sbnil);
    let mix = cx.elta("StepBranchList");
    cx.funa("sbCons", vec![lref(step), lref(sbnil), q(1, 1)], mix);
    let sv = cx.elta("ScaleView");
    cx.funa("mkScaleView", vec![lref(mix), lref(pzero)], sv);
    cx.ops.push(Op::Rela {
        rel: cx.fun_ref("tr_scale"),
        args: vec![lref(sv), lref(tr)],
    });

    // Plate + constant-1 feature + hagSum certificate.
    let plate = cx.elta("HPlate");
    cx.attr("HPlate/sys", plate, lref(sys));
    cx.ops.push(Op::Rela {
        rel: cx.fun_ref("hplate_token"),
        args: vec![lref(plate), lref(tk)],
    });
    let c1 = cx.elta("Poly");
    cx.funa("pTerm", vec![q(1, 1), shape(&[0]), lref(pzero)], c1);
    let feat = cx.elta("HFeature");
    cx.attr("HFeature/plate", feat, lref(plate));
    cx.attr("HFeature/poly", feat, lref(c1));
    let kind = cx.elta("HAggKind");
    cx.funa("hagSum", vec![], kind);
    let cert = cx.elta("HCert");
    cx.attr("HCert/sys", cert, lref(sys));
    cx.attr("HCert/kind", cert, lref(kind));
    cx.ops.push(Op::Rela {
        rel: cx.fun_ref("hcert_feat"),
        args: vec![lref(cert), lref(feat)],
    });

    // The footprint-row roster on the drain transition.
    let mut row_ids = Vec::new();
    for p in pols {
        let row = cx.elta("HFootprintRow");
        cx.attr("HFootprintRow/cert", row, lref(cert));
        cx.attr("HFootprintRow/tr", row, lref(tr));
        let pol = cx.elta("HRowPolarity");
        match p {
            RowPol::Safety => cx.funa("hrpSafety", vec![], pol),
            RowPol::Gap(n, d) => {
                cx.funa("hrpGap", vec![], pol);
                cx.attr("HFootprintRow/gap", row, q(*n, *d));
            }
            RowPol::Drop(n, d) => {
                cx.funa("hrpDropAtMost", vec![], pol);
                cx.attr("HFootprintRow/ubound", row, q(*n, *d));
            }
        }
        cx.attr("HFootprintRow/polarity", row, lref(pol));
        row_ids.push(row);
    }
    Base {
        cert,
        rows: row_ids,
    }
}

fn cell(v: &Value) -> Vec<u8> {
    let mut buf = Vec::new();
    v.encode(&mut buf);
    buf
}

fn verdict(provider: &QtslGroundProvider, rel: &str, args: &[Value], rows: &CertRows) -> Verdict {
    let local = provider
        .local_by_name(rel)
        .unwrap_or_else(|| panic!("`{rel}` claimed"));
    let cells: Vec<Vec<u8>> = args.iter().map(cell).collect();
    let refs: Vec<&[u8]> = cells.iter().map(|c| c.as_slice()).collect();
    provider.filter_rows(local, &refs, rows)
}

fn coverage(pols: &[RowPol]) -> Verdict {
    let (idx, provider) = setup();
    let mut cx = Cx::new(&idx);
    let base = build_drain(&mut cx, pols);
    let rows = cx.rows();
    verdict(&provider, "qtsl_hplate_coverage", &[lref(base.cert)], &rows)
}

/// Control: an upper (safety) row covers the may-touch drain — and the
/// vocabulary extension itself perturbs nothing.
#[test]
fn coverage_upper_row_covers_under_extended_vocabulary() {
    let v = coverage(&[RowPol::Safety]);
    assert!(matches!(v, Verdict::Holds), "expected Holds, got {v:?}");
}

/// THE KILL: a may-touch transition whose ONLY footprint row is
/// dropAtMost is NOT covered — a drop-by-at-most row bounds nothing
/// above. (Before the guard, the polarity-blind covering count
/// returned Holds here; that unguarded collect is this battery's
/// mutant, and this test is its witness.)
#[test]
fn coverage_dropatmost_only_row_does_not_cover() {
    let v = coverage(&[RowPol::Drop(0, 1)]);
    assert!(matches!(v, Verdict::Fails), "expected Fails, got {v:?}");
}

/// The pair idiom survives the guard: exact conservation as
/// `{hrpSafety, hrpDropAtMost(0)}` on one (cert, transition) — the
/// guard filters the drop half out of the covering count; it never
/// refuses its presence.
#[test]
fn coverage_safety_drop_pair_covers() {
    let v = coverage(&[RowPol::Safety, RowPol::Drop(0, 1)]);
    assert!(matches!(v, Verdict::Holds), "expected Holds, got {v:?}");
}

/// The pair idiom, gap side: displacement exactly −1 as `{hrpGap(1),
/// hrpDropAtMost(1)}` — the gap half covers.
#[test]
fn coverage_gap_drop_pair_covers() {
    let v = coverage(&[RowPol::Gap(1, 1), RowPol::Drop(1, 1)]);
    assert!(matches!(v, Verdict::Holds), "expected Holds, got {v:?}");
}

/// The footprint SEQUENT on a dropAtMost row refuses loudly, naming
/// the successor: TRUE would be unsound (the sides are swapped),
/// FALSE would mis-decide a sequent that may hold.
#[test]
fn footprint_sequent_on_dropatmost_row_refuses_named() {
    let (idx, provider) = setup();
    let mut cx = Cx::new(&idx);
    let base = build_drain(&mut cx, &[RowPol::Drop(0, 1)]);
    let rows = cx.rows();
    let v = verdict(
        &provider,
        "qtsl_hplate_footprint",
        &[lref(base.rows[0])],
        &rows,
    );
    match v {
        Verdict::Refused(why) => assert!(
            why.contains("hrpSafety/hrpGap"),
            "refusal names the upper-polarity fragment: {why}"
        ),
        other => panic!("expected a named refusal, got {other:?}"),
    }
}
