//! The plugin seam exercised end to end: the provider's claims
//! adjudicated by the engine's binder, the engine-enforced scope
//! routing, and the specimen pair — a certificate side-condition
//! verified and its tampered variants rejected/refused — through the
//! provider's full evaluation path.

mod common;

use common::{ev_elems, provider, stack, REV, STACK};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use geolog_ground_api::{
    BindStatus, Binder, DeclId, DeclSignature, EvalCtx, GroundOracle, GroundProvider, ResolvedDecl,
    RowView, Verdict,
};
use qtsl_geolog_provider::rowctx::CertRows;

/// Mint resolved declarations straight from the provider's own claims
/// (name + field/sort names), pinned to synthetic identities, each
/// carrying the committed-semantics revision the provider was built
/// with.
fn decls_from_claims(rev: Option<[u8; 32]>) -> Vec<ResolvedDecl> {
    provider()
        .relations()
        .iter()
        .enumerate()
        .map(|(i, e)| ResolvedDecl {
            id: DeclId {
                commit: [0xDC; 32],
                op: i as u32,
            },
            name: e.name.to_string(),
            sig: DeclSignature {
                fields: e
                    .fields
                    .iter()
                    .map(|(n, s)| (n.to_string(), s.to_string()))
                    .collect(),
                codomain: None,
            },
            semantics_rev: rev,
            is_function: false,
        })
        .collect()
}

#[test]
fn entry_count_matches_lib_headline() {
    // The lib.rs "claimed roster (N relations)" headline cites
    // ENTRY_COUNT as its computed authority — and went stale three
    // times across family generations (66, 92, 116) because nothing
    // failed when it drifted. This pin makes headline updates an
    // artifact pair: bump both in the same commit.
    assert_eq!(
        qtsl_geolog_provider::provider::ENTRY_COUNT,
        126,
        "ENTRY_COUNT moved — update the lib.rs roster headline (and \
         this pin) in the same commit"
    );
}

#[test]
fn binder_implements_every_claimed_entry() {
    let decls = decls_from_claims(Some(REV));
    let binder = Binder::bind(&decls, vec![provider()]).expect("no conflicts");
    assert_eq!(
        decls.len(),
        99,
        "the claimed roster: 16 applicability + 2 atomic + 1 recompute \
         + 6 masks + 4 system-spec (poly canonical form, sys causal, \
         sys W3, flatten) + 8 problog + 6 conclusion forms (barycentric \
         halfspace + the four cell-schema forms + the LiRPA \
         conclusion form) + 2 block-lattice + \
         1 enclosure + 4 carillon discharge-plan (cell cover, dbar \
         closure, gap-A, floor boxes) + 4 surgery (conjunctAt, \
         conjReplace, substituteInFormula, applyPredicateToTerm) + \
         2 promise interface-confinement (promiseContractConfined, \
         promiseWiresSeparated) + 3 predicate semantic classes \
         (isConicPredicate, isConvexPredicate, \
         isUpwardClosedConicPredicate) + 3 Bernstein-cone \
         (allForwardDiffBernCoeffsSatisfyP, coverInfeasibilityValid, \
         allForwardDiffBernIntvEnclosuresSatisfyP) \
         + 1 deadline table (qtsl_deadline_table) \
         + 5 transition/bag well-formedness (qtsl_tr_content, \
         qtsl_tr_grain, qtsl_tr_endo, qtsl_massone, qtsl_bag_wf) \
         + 5 guarded-specification (qtsl_init_member, \
         qtsl_warrant_member, qtsl_spec_wf, qtsl_cert_claim_wf, \
         qtsl_base_exact) \
         + 7 angelic-selection (qtsl_asel_reach, _cover, _enabled, \
         _closed, _ratecap, _relay, _attach) \
         + 1 hole-count (qtsl_hole_count, the seat-regret linearity \
         ledger) \
         + 2 store-seam circuit (qtsl_kcite_wf, qtsl_gate_scalar — \
         the grain/endo circuit arms ride the \
         trwf entries by dispatch routing, no rows of their own) \
         + 9 NN conclusion forms (reluPremNonnegForm, \
         reluPremNonposForm, reluOutEqInputForm, reluOutZeroForm, \
         reluOutNonnegForm, reluOutDominatesForm, lirpaPremLoForm, \
         lirpaPremHiForm, lirpaSandwichForm) \
         + 2 semiring-cell (qtsl_contract_param, qtsl_contract_cell \
         v1) \
         + 1 MarkFlow walk (qtsl_wire_markflow) \
         + 2 carved-window pair (qtsl_dwell_gate, qtsl_tr_ratecap) \
         + 1 causality walk (qtsl_wire_causality, the ∀-face \
         sibling) \
         + 1 LRA-battery walk (qtsl_avg_battery — the structural \
         stratum; its claim relation awaits the rules-as-rows fan's \
         mint, so only fixtures stage it today) \
         — the fixture stages the Bag and \
         ProbLog vocabularies only among the recompute kits"
    );
    for d in &decls {
        let report = &binder.statuses[&d.id];
        assert!(
            matches!(report.status, BindStatus::ImplementedRel(_)),
            "`{}` should bind Implemented, got {:?}",
            d.name,
            report.status
        );
        assert!(report.drift.is_empty(), "`{}` clean bind", d.name);
    }
    // The registry artefact renders one line per adjudicated entry.
    assert_eq!(binder.registry_lines(&decls).len(), decls.len());
}

#[test]
fn unresolved_family_defers_as_unclaimed() {
    // The Morse-readout relation is DECLARED but its vocabulary is
    // absent from the fixture's revisions, so the provider does not
    // claim it — and a declaration for it defers at the binder (no
    // claimant): declared-but-unbound, safe-fail, with the reason
    // recorded on the vocabulary.
    let decl = ResolvedDecl {
        id: DeclId {
            commit: [0xDD; 32],
            op: 0,
        },
        name: "qtsl_morse_readout".to_string(),
        sig: DeclSignature {
            fields: vec![
                ("dag".into(), "QDag".into()),
                ("h".into(), "QCellMap".into()),
                ("lat".into(), "QBlockLattice".into()),
                ("rho".into(), "QVertexRegionList".into()),
            ],
            codomain: None,
        },
        semantics_rev: Some(REV),
        is_function: false,
    };
    let binder = Binder::bind(std::slice::from_ref(&decl), vec![provider()]).expect("no conflicts");
    assert!(
        matches!(
            binder.statuses[&decl.id].status,
            BindStatus::Deferred { .. }
        ),
        "unclaimed family must defer"
    );
    assert!(provider()
        .vocab()
        .notes
        .iter()
        .any(|n| n.contains("morse-readout")));
}

#[test]
fn semantics_gating_defers_never_guesses() {
    // Committed semantics at a revision the provider was not written
    // against: Deferred. No committed semantics row at all: Deferred.
    for rev in [Some([0x99; 32]), None] {
        let decls = decls_from_claims(rev);
        let binder = Binder::bind(&decls, vec![provider()]).expect("no conflicts");
        for d in &decls {
            assert!(
                matches!(binder.statuses[&d.id].status, BindStatus::Deferred { .. }),
                "`{}` must defer under rev {rev:?}",
                d.name
            );
        }
    }
}

#[test]
fn signature_drift_refuses_loudly() {
    // Code and theory disagreeing on a sort name is the drift alarm:
    // Refused, distinct from Deferred.
    let mut decls = decls_from_claims(Some(REV));
    decls[0].sig.fields[0].1 = "Q".to_string(); // declared sort drifted
    let binder = Binder::bind(&decls, vec![provider()]).expect("refusal, not conflict");
    let report = &binder.statuses[&decls[0].id];
    assert!(
        matches!(report.status, BindStatus::Refused { .. }),
        "drifted signature must refuse, got {:?}",
        report.status
    );
    assert_eq!(report.drift.len(), 1);
}

/// A probe-only row view (the seam's current surface).
struct Probe;
impl RowView for Probe {
    fn probe(&self) -> u64 {
        7
    }
}

#[test]
fn snapshot_scope_is_engine_enforced_and_refusals_are_named() {
    let decls = decls_from_claims(Some(REV));
    let binder = Binder::bind(&decls, vec![provider()]).expect("no conflicts");
    let rel = match binder.statuses[&DeclId {
        commit: [0xDC; 32],
        op: 0,
    }]
        .status
    {
        BindStatus::ImplementedRel(id) => id,
        ref s => panic!("expected a bound relation, got {s:?}"),
    };
    // Without a snapshot: the ENGINE refuses (snapshot-scoped relation,
    // pure context) — the provider is not consulted.
    let one = {
        let mut buf = Vec::new();
        Value::Ref(ElemRef::Local(0)).encode(&mut buf);
        buf
    };
    let v = binder.filter(rel, &[&one, &one], &EvalCtx::Pure);
    match v {
        Verdict::Refused(reason) => assert!(
            reason.contains("without a row snapshot"),
            "engine-side scope refusal, got: {reason}"
        ),
        other => panic!("expected refusal, got {other:?}"),
    }
    // With the probe-only snapshot: the PROVIDER refuses, naming the
    // typed-row gap and the available full path — conservative and
    // loud, never a guessed verdict.
    let probe = Probe;
    let v = binder.filter(rel, &[&one, &one], &EvalCtx::Snapshot(&probe));
    match v {
        Verdict::Refused(reason) => assert!(
            reason.contains("filter_rows"),
            "provider refusal names the full path, got: {reason}"
        ),
        other => panic!("expected refusal, got {other:?}"),
    }
    // No order semantics anywhere in the roster.
    assert!(binder.cmp(rel, &one, &one).is_err());
    assert!(binder.monotone_key(rel, &one).is_err());
}

// ---------------------------------------------------------------- the
// specimen pair: verified / forged / tampered, at the instance-cell
// level through the provider's full evaluation path.

/// Emit a PSD T-witness node: A = [[2,-1],[-1,2]] (positive definite),
/// Z = [[1,1/2],[0,1]] — A·Z lower-triangular with positive diagonal.
/// `forge` swaps in a matrix that is NOT positive definite.
fn psd_t_body(forge: bool) -> (Vec<Op>, u32) {
    let s = stack();
    let f = |name: &str| {
        let chid = s.fun(name).expect(name).chid;
        ElemRef::External {
            dep_index: 0,
            counter: chid.1,
        }
    };
    let sort = |name: &str| {
        let chid = s.sort(name).expect(name);
        ElemRef::External {
            dep_index: 0,
            counter: chid.1,
        }
    };
    let mut ops = Vec::new();
    let node = ops.len() as u32;
    ops.push(Op::Elta {
        sort: sort("PPsdCertT"),
    });
    let lref = |e: u32| Value::Ref(ElemRef::Local(e));
    let q_tensor = |vals: &[(i64, u64)]| {
        Value::Lit(Literal::tensor_inline_q(&[2, 2], vals).expect("inline tensor"))
    };
    ops.push(Op::Funa {
        fun: f("PPsdCertT/n"),
        args: vec![lref(node)],
        value: Value::Lit(Literal::nat(2)),
    });
    let a = if forge {
        // [[1,-1],[-1,1]] is singular: no valid witness exists for it,
        // and this Z in particular fails the triangular check.
        q_tensor(&[(1, 1), (-1, 1), (-1, 1), (1, 1)])
    } else {
        q_tensor(&[(2, 1), (-1, 1), (-1, 1), (2, 1)])
    };
    ops.push(Op::Funa {
        fun: f("PPsdCertT/A"),
        args: vec![lref(node)],
        value: a,
    });
    ops.push(Op::Funa {
        fun: f("PPsdCertT/Z"),
        args: vec![lref(node)],
        value: q_tensor(&[(1, 1), (1, 2), (0, 1), (1, 1)]),
    });
    (ops, node)
}

#[test]
fn psd_witness_specimen_verified_forged_and_tampered() {
    // Verified: the witness relation holds on the sound instance.
    let (ops, node) = psd_t_body(false);
    let rows = CertRows::from_ops(&ops, [0xAB; 32], &[STACK]);
    assert_eq!(ev_elems("psdCertTWitness", &[node], &rows), Ok(true));

    // Forged: a non-PD matrix under the same shape decides FALSE — the
    // checker catches the forgery, it does not refuse it.
    let (ops, node) = psd_t_body(true);
    let rows = CertRows::from_ops(&ops, [0xAB; 32], &[STACK]);
    assert_eq!(ev_elems("psdCertTWitness", &[node], &rows), Ok(false));

    // Tampered: truncating the argument cell REFUSES at the decode
    // boundary with a named reason — before any arithmetic could be
    // misled.
    let (ops, node) = psd_t_body(false);
    let rows = CertRows::from_ops(&ops, [0xAB; 32], &[STACK]);
    let p = provider();
    let local = p.local_by_name("psdCertTWitness").expect("claimed");
    let mut cell = Vec::new();
    Value::Ref(ElemRef::Local(node)).encode(&mut cell);
    let truncated = &cell[..cell.len() - 1];
    match p.filter_rows(local, &[truncated], &rows) {
        Verdict::Refused(reason) => {
            assert!(
                reason.contains("decode refused") || reason.contains("trailing"),
                "named decode failure, got: {reason}"
            );
        }
        other => panic!("tampered cell must refuse, got {other:?}"),
    }
    // Trailing garbage past one canonical value refuses too.
    let mut padded = cell.clone();
    padded.push(0);
    match p.filter_rows(local, &[&padded], &rows) {
        Verdict::Refused(reason) => {
            assert!(reason.contains("trailing"), "named reason, got: {reason}")
        }
        other => panic!("padded cell must refuse, got {other:?}"),
    }
}

#[test]
fn exact_rational_evaluation_specimen() {
    // Closed exact-Q evaluation through provider dispatch:
    // (1/2)·4 − 1 = 1 holds; the tampered comparison fails; an open
    // term is decidedly not closed.
    let s = stack();
    let f = |name: &str| {
        let chid = s.fun(name).expect(name).chid;
        ElemRef::External {
            dep_index: 0,
            counter: chid.1,
        }
    };
    let sort = |name: &str| {
        let chid = s.sort(name).expect(name);
        ElemRef::External {
            dep_index: 0,
            counter: chid.1,
        }
    };
    let mut ops: Vec<Op> = Vec::new();
    let lref = |e: u32| Value::Ref(ElemRef::Local(e));
    let elta = |ops: &mut Vec<Op>, sname: &str| {
        let e = ops.len() as u32;
        ops.push(Op::Elta { sort: sort(sname) });
        e
    };
    let ctor = |ops: &mut Vec<Op>, sname: &str, fname: &str, args: Vec<Value>| {
        let e = {
            let e = ops.len() as u32;
            ops.push(Op::Elta { sort: sort(sname) });
            e
        };
        ops.push(Op::Funa {
            fun: f(fname),
            args,
            value: lref(e),
        });
        e
    };
    let q = |n: i64, d: u64| Value::Lit(Literal::q(n, d).expect("canonical q"));
    let half = ctor(&mut ops, "Term", "TConst", vec![q(1, 2)]);
    let four = ctor(&mut ops, "Term", "TConst", vec![q(4, 1)]);
    let one = ctor(&mut ops, "Term", "TConst", vec![q(1, 1)]);
    let prod = ctor(&mut ops, "Term", "TMul", vec![lref(half), lref(four)]);
    let lhs = ctor(&mut ops, "Term", "TSub", vec![lref(prod), lref(one)]);
    let wire = elta(&mut ops, "Wire");
    let open = ctor(&mut ops, "Term", "TVar", vec![lref(wire)]);
    let rows = CertRows::from_ops(&ops, [0xAC; 32], &[STACK]);

    let ev3 = |bowtie: u64, l: u32, r: u32| {
        let vals = [
            Value::Lit(Literal::nat(bowtie)),
            Value::Ref(ElemRef::Local(l)),
            Value::Ref(ElemRef::Local(r)),
        ];
        let refs: Vec<&Value> = vals.iter().collect();
        common::ev("constExactEvalTrue", &refs, &rows)
    };
    assert_eq!(ev3(2, lhs, one), Ok(true), "(1/2)·4 − 1 = 1, exactly");
    assert_eq!(ev3(0, lhs, one), Ok(false), "1 < 1 is false");
    assert_eq!(ev3(2, open, one), Ok(false), "open term is not closed");
}
