//! The morse-readout recognizer's post-grid atom hop against the REAL
//! baked event-4 closure:
//! `SAtomLE{c, o: oPoly(x_k)}` classifies box-aligned exactly as the
//! legacy direct-poly spelling did, and a non-polynomial observable
//! (`oGate`) classifies Opaque — total classification, never a
//! refusal on a definite non-box shape. (The legacy arm's regression
//! coverage is the existing synthetic-index morse suite, which still
//! resolves through the direct shape — dual-pin by construction.)

use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::morse::{classify_region, RegionClass, RegionVocab};
use qtsl_geolog_provider::reprovocab::baked::{
    baked_vocab_from_container, qc_v1_container_bytes, BakedVocab, BAKED_QC_V1_REV,
};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::{DomainSig, SortKey};
use std::collections::HashSet;

fn lref(n: u32) -> Value {
    Value::Ref(ElemRef::Local(n))
}

/// A RegionVocab over the baked index, assembled the way the builders
/// do (fields are public exactly for this injection pattern).
fn region_vocab(vocab: &BakedVocab) -> RegionVocab {
    let fun = |name: &str| vocab.index.fun(name).unwrap_or_else(|| panic!("{name}"));
    let statef_sort = {
        let d = fun("STrue");
        match d.codomain {
            Some(SortKey::Elem(c)) => c,
            _ => panic!("STrue codomain"),
        }
    };
    let sflist_sort = match &fun("SAnd").domain {
        DomainSig::Unary(SortKey::Elem(c)) => *c,
        _ => panic!("SAnd domain"),
    };
    let stateobs_sort = match fun("oPoly").codomain {
        Some(SortKey::Elem(c)) => c,
        _ => panic!("oPoly codomain"),
    };
    let poly_sort = match fun("pZero").codomain {
        Some(SortKey::Elem(c)) => c,
        _ => panic!("pZero codomain"),
    };
    let roster = |sort| -> HashSet<_> {
        vocab
            .index
            .funs
            .iter()
            .filter(|d| {
                !d.relational && !d.name.contains('/') && d.codomain == Some(SortKey::Elem(sort))
            })
            .map(|d| d.chid)
            .collect()
    };
    RegionVocab {
        s_true: fun("STrue").chid,
        s_and: fun("SAnd").chid,
        s_atom_le: fun("SAtomLE").chid,
        s_atom_ge: fun("SAtomGE").chid,
        sl_nil: fun("slNil").chid,
        sl_cons: fun("slCons").chid,
        p_zero: fun("pZero").chid,
        p_term: fun("pTerm").chid,
        statef_roster: roster(statef_sort),
        sflist_roster: roster(sflist_sort),
        poly_roster: roster(poly_sort),
        o_poly: Some(fun("oPoly").chid),
        stateobs_roster: roster(stateobs_sort),
    }
}

/// Rows for the region `SAnd([x_0 ≥ 0, x_0 ≤ 1])` (a bounded,
/// cut-aligned box) with both atoms' observables per the knob; returns
/// (ops, region element).
fn region_ops(vocab: &BakedVocab, gate_observable: bool) -> (Vec<Op>, u32) {
    let fun = |name: &str| -> ElemRef {
        let d = vocab.index.fun(name).unwrap();
        ElemRef::External {
            dep_index: 0,
            counter: d.chid.1,
        }
    };
    let sort = |name: &str| -> ElemRef {
        let chid = vocab.index.sort(name).unwrap();
        ElemRef::External {
            dep_index: 0,
            counter: chid.1,
        }
    };
    let mut ops: Vec<Op> = Vec::new();
    let mut next: u32 = 0;
    let mut elta = |ops: &mut Vec<Op>, s: &str| -> u32 {
        ops.push(Op::Elta { sort: sort(s) });
        next += 1;
        next - 1
    };
    let pz = elta(&mut ops, "Poly");
    ops.push(Op::Funa {
        fun: fun("pZero"),
        args: vec![],
        value: lref(pz),
    });
    let x0 = elta(&mut ops, "Poly");
    ops.push(Op::Funa {
        fun: fun("pTerm"),
        args: vec![
            Value::Lit(Literal::q(1, 1).unwrap()),
            Value::Lit(Literal::shape(&[1])),
            lref(pz),
        ],
        value: lref(x0),
    });
    // The observable (shared by both atoms).
    let ob = elta(&mut ops, "StateObservable");
    if gate_observable {
        let g = elta(&mut ops, "HypernetRef");
        ops.push(Op::Funa {
            fun: fun("oGate"),
            args: vec![lref(g)],
            value: lref(ob),
        });
    } else {
        ops.push(Op::Funa {
            fun: fun("oPoly"),
            args: vec![lref(x0)],
            value: lref(ob),
        });
    }
    let a_ge = elta(&mut ops, "StatePred");
    ops.push(Op::Funa {
        fun: fun("SAtomGE"),
        args: vec![Value::Lit(Literal::q(0, 1).unwrap()), lref(ob)],
        value: lref(a_ge),
    });
    let a_le = elta(&mut ops, "StatePred");
    ops.push(Op::Funa {
        fun: fun("SAtomLE"),
        args: vec![Value::Lit(Literal::q(1, 1).unwrap()), lref(ob)],
        value: lref(a_le),
    });
    let nil = elta(&mut ops, "StatePredList");
    ops.push(Op::Funa {
        fun: fun("slNil"),
        args: vec![],
        value: lref(nil),
    });
    let l1 = elta(&mut ops, "StatePredList");
    ops.push(Op::Funa {
        fun: fun("slCons"),
        args: vec![lref(a_le), lref(nil)],
        value: lref(l1),
    });
    let l2 = elta(&mut ops, "StatePredList");
    ops.push(Op::Funa {
        fun: fun("slCons"),
        args: vec![lref(a_ge), lref(l1)],
        value: lref(l2),
    });
    let region = elta(&mut ops, "StatePred");
    ops.push(Op::Funa {
        fun: fun("SAnd"),
        args: vec![lref(l2)],
        value: lref(region),
    });
    (ops, region)
}

#[test]
fn opoly_atom_classifies_box_aligned_and_ogate_opaque() {
    let vocab = baked_vocab_from_container(qc_v1_container_bytes(), BAKED_QC_V1_REV)
        .expect("qc chain derives");
    let rv = region_vocab(&vocab);
    // One axis with cuts {0, 1, 2}: two cells; x_0 <= 1 selects cell 0.
    let grid_counts = [3u64];
    let grid = vec![vec![
        Literal::q(0, 1).unwrap(),
        Literal::q(1, 1).unwrap(),
        Literal::q(2, 1).unwrap(),
    ]];

    let (ops, region) = region_ops(&vocab, false);
    let rows = CertRows::from_ops(&ops, [0xAB; 32], &[BAKED_QC_V1_REV]);
    let mut steps = 0usize;
    let class = classify_region(
        &rv,
        &rows,
        &mut steps,
        1 << 16,
        region,
        1,
        &grid_counts,
        &grid,
    )
    .expect("classification is definite");
    assert_eq!(
        class,
        RegionClass::BoxAligned(vec![0]),
        "the oPoly hop reaches the monomial and the box aligns"
    );

    let (ops, region) = region_ops(&vocab, true);
    let rows = CertRows::from_ops(&ops, [0xAB; 32], &[BAKED_QC_V1_REV]);
    let mut steps = 0usize;
    let class = classify_region(
        &rv,
        &rows,
        &mut steps,
        1 << 16,
        region,
        1,
        &grid_counts,
        &grid,
    )
    .expect("classification is definite");
    assert_eq!(
        class,
        RegionClass::Opaque,
        "a gate observable has no polynomial reading — Opaque, not a refusal"
    );
}
