//! Acceptance for the derived baked-pair vocabulary
//! (`reprovocab::baked`): round-trips from the production store's own
//! extracts, the pins-file tie, and the refusal battery.

use qtsl_geolog_provider::container::{parse_container, verify_commits};
use qtsl_geolog_provider::reprovocab::baked::{
    baked_vocab_from_container, dc_v1_container_bytes, qc_v1_container_bytes, resolve_baked_rev,
    BakedPin, BAKED_COMPARISONS_CHID, BAKED_DC_V1_REV, BAKED_GENESIS_CHID, BAKED_PRIMARY_EVENT,
    BAKED_QC_V1_REV, BAKED_ROSTER,
};
use qtsl_geolog_provider::QtslVocab;

fn hex(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// The pins record's `closure <c> shape theories=N` field — the
/// authority the derivation-shape assertions tie to, so a mint swap
/// updates them by updating the pins file alone.
fn pinned_shape_theories(closure: &str) -> usize {
    let pins = include_str!("../../../theories/pins/baked_v1_pins.txt");
    let key = format!("closure {closure} shape");
    pins.lines()
        .find(|l| l.starts_with(&key))
        .unwrap_or_else(|| panic!("pins file carries `{key}`"))
        .split_whitespace()
        .find_map(|t| t.strip_prefix("theories="))
        .expect("shape line carries theories=")
        .parse()
        .expect("theories= is a count")
}

/// The four pinned chids match `theories/pins/baked_v1_pins.txt`
/// byte for byte (the cross-artifact tie: a drifted constant fails
/// against the committed pins file, and vice versa).
#[test]
fn pins_file_tie() {
    let pins = include_str!("../../../theories/pins/baked_v1_pins.txt");
    let field = |line_key: &str| -> String {
        pins.lines()
            .find(|l| l.starts_with(line_key))
            .unwrap_or_else(|| panic!("pins file carries `{line_key}`"))
            .split_whitespace()
            .last()
            .expect("pin line has a value")
            .to_string()
    };
    assert_eq!(field("closure qc revision"), hex(&BAKED_QC_V1_REV));
    assert_eq!(field("closure dc revision"), hex(&BAKED_DC_V1_REV));
    assert_eq!(field("golden genesis"), hex(&BAKED_GENESIS_CHID));
    assert_eq!(
        field("golden ground_comparisons"),
        hex(&BAKED_COMPARISONS_CHID)
    );
}

/// The qc chain container (the production store's extract) derives:
/// envelope verification, full-conformance meta-schema load, and an
/// index whose shape matches the pins file's recorded closure shape.
#[test]
fn qc_chain_derives() {
    let vocab = baked_vocab_from_container(qc_v1_container_bytes(), BAKED_QC_V1_REV)
        .expect("qc chain derives");
    assert_eq!(vocab.revision, BAKED_QC_V1_REV);
    // The pins file records the closure shape (`closure qc shape`).
    assert_eq!(
        vocab.stats.theories,
        pinned_shape_theories("qc"),
        "qc theory count matches the pins record's shape line"
    );
    assert!(vocab.stats.funs > 0 && vocab.stats.sorts > 0);
    // The F2 fluid claim species live in the baked tower.
    for name in [
        "farkasCombinationValid",
        "constExactEvalTrue",
        "syzygyCombinationValid",
        "syzygyConclusionFormRel",
    ] {
        let d = vocab
            .index
            .fun(name)
            .expect("baked tower declares the claim");
        assert!(
            d.relational && d.side_condition,
            "{name} is a side condition"
        );
        assert!(vocab.claims.iter().any(|c| c == name));
    }
    eprintln!(
        "qc stats: theories={} sorts={} funs={} fields={} objects={} claims={}",
        vocab.stats.theories,
        vocab.stats.sorts,
        vocab.stats.funs,
        vocab.stats.fields,
        vocab.stats.objects,
        vocab.claims.len()
    );
    // Which provider families resolve over the derived index — print
    // the notes so the record carries the reasons either way.
    let qv = QtslVocab::build(&[&vocab.index]);
    eprintln!("qc vocab notes: {:#?}", qv.notes);
    eprintln!(
        "qc resolved: bl={} mask={} enclosure={} carillon={} deadline={}",
        qv.bl.is_some(),
        qv.mask.is_some(),
        qv.enclosure.is_some(),
        qv.carillon.is_some(),
        qv.deadline.is_some()
    );
    assert!(
        qv.bl.is_some(),
        "BL family resolves over baked qc: {:?}",
        qv.notes
    );
}

/// The dc chain derives likewise (11 theories: qc + Dtmc).
#[test]
fn dc_chain_derives() {
    let vocab = baked_vocab_from_container(dc_v1_container_bytes(), BAKED_DC_V1_REV)
        .expect("dc chain derives");
    assert_eq!(vocab.revision, BAKED_DC_V1_REV);
    assert_eq!(
        vocab.stats.theories,
        pinned_shape_theories("dc"),
        "dc theory count matches the pins record's shape line"
    );
    let qv = QtslVocab::build(&[&vocab.index]);
    eprintln!("dc vocab notes: {:#?}", qv.notes);
    eprintln!(
        "dc resolved: bl={} deadline={}",
        qv.bl.is_some(),
        qv.deadline.is_some()
    );
    assert!(
        qv.bl.is_some(),
        "BL family resolves over baked dc: {:?}",
        qv.notes
    );
}

/// Determinism: two independent derivations construct the identical
/// index (same names, same chids, same order).
#[test]
fn derivation_deterministic() {
    let a = baked_vocab_from_container(qc_v1_container_bytes(), BAKED_QC_V1_REV).unwrap();
    let b = baked_vocab_from_container(qc_v1_container_bytes(), BAKED_QC_V1_REV).unwrap();
    assert_eq!(a.index.funs.len(), b.index.funs.len());
    for (fa, fb) in a.index.funs.iter().zip(b.index.funs.iter()) {
        assert_eq!(fa.name, fb.name);
        assert_eq!(fa.chid, fb.chid);
        assert_eq!(fa.domain, fb.domain);
    }
    assert_eq!(a.claims, b.claims);
}

/// Asking the qc container for the dc revision refuses loudly (the
/// pin gate: a chain container only yields the vocabulary it was
/// pinned to carry).
#[test]
fn wrong_pin_refuses() {
    let err = baked_vocab_from_container(qc_v1_container_bytes(), BAKED_DC_V1_REV)
        .expect_err("qc chain does not carry the dc revision");
    assert!(
        err.contains("chain_missing_revision"),
        "refusal names the missing revision: {err}"
    );
}

/// A tampered commit body refuses at the envelope layer (body-hash
/// binding), never reaching derivation.
#[test]
fn tampered_body_refuses() {
    let mut bytes = qc_v1_container_bytes().to_vec();
    // Flip one byte deep in the last commit's body region (the
    // container tail is body bytes; the final byte is body content).
    let n = bytes.len();
    bytes[n - 100] ^= 0x01;
    let c = parse_container(&bytes).expect("grammar still parses");
    let err = match verify_commits(&c, &[]) {
        Ok(_) => panic!("tampered body must refuse"),
        Err(e) => e,
    };
    assert!(
        err.contains("body_hash") || err.contains("body"),
        "refusal names the body binding: {err}"
    );
}

/// The reserved hole-wire spelling under the DERIVED baked index
/// (`formrows::HOLE_WIRE_INDEX`): the baked closures declare no hole
/// constructor, and the bl re-emission producers spell the predicate hole
/// as `TVar [nat:4294967295]` — the row-grain transport of the Lean
/// route-d projection (`VfTHole ↦ TmVar 4294967295`). Positive: a
/// conic predicate over the reserved spelling classifies and HOLDS.
/// Control: a non-reserved literal wire index is NOT the hole — the
/// predicate classifies outside the fragment and DECIDES FALSE.
#[test]
fn reserved_hole_wire_classifies_under_baked() {
    use geolog_envelope::body::Op;
    use geolog_envelope::{ElemRef, Literal, Value};
    use geolog_ground_api::Verdict;
    use qtsl_geolog_provider::rowctx::CertRows;
    use qtsl_geolog_provider::QtslGroundProvider;

    let vocab = baked_vocab_from_container(qc_v1_container_bytes(), BAKED_QC_V1_REV).unwrap();
    let qv = QtslVocab::build(&[&vocab.index]);
    assert!(qv.bl.is_some(), "BL family resolves: {:?}", qv.notes);
    let provider = QtslGroundProvider::new(vec![[0x2f; 32]], qv);
    let fun = |name: &str| -> ElemRef {
        let d = vocab
            .index
            .fun(name)
            .unwrap_or_else(|| panic!("baked tower declares `{name}`"));
        assert_eq!(d.chid.0, BAKED_QC_V1_REV);
        ElemRef::External {
            dep_index: 0,
            counter: d.chid.1,
        }
    };
    let sort = |name: &str| -> ElemRef {
        let chid = vocab.index.sort(name).expect("sort");
        ElemRef::External {
            dep_index: 0,
            counter: chid.1,
        }
    };
    let lref = |n: u32| Value::Ref(ElemRef::Local(n));

    // Rows: predicate = FAtomLE(<hole spelling>, TConst 0).
    let body = |wire_index: u64| -> Vec<Op> {
        vec![
            Op::Elta { sort: sort("Term") }, // L0: the hole term
            Op::Funa {
                fun: fun("TVar"),
                args: vec![Value::Lit(Literal::nat(wire_index))],
                value: lref(0),
            },
            Op::Elta { sort: sort("Term") }, // L2: the bound
            Op::Funa {
                fun: fun("TConst"),
                args: vec![Value::Lit(Literal::q(0, 1).unwrap())],
                value: lref(2),
            },
            Op::Elta {
                sort: sort("Formula"),
            }, // L4: the predicate
            Op::Funa {
                fun: fun("FAtomLE"),
                args: vec![lref(0), lref(2)],
                value: lref(4),
            },
        ]
    };
    let deps = vec![BAKED_QC_V1_REV];
    let local = provider
        .local_by_name("isConicPredicate")
        .expect("isConicPredicate claimed");
    let cell = {
        let mut buf = Vec::new();
        lref(4).encode(&mut buf);
        buf
    };

    // Positive: the reserved index classifies as the hole; LE at zero
    // is conic (classifyPredAtom's LE arm).
    let ops = body(qtsl_geolog_provider::formrows::HOLE_WIRE_INDEX);
    let rows = CertRows::from_ops(&ops, [0xAB; 32], &deps);
    assert!(
        matches!(provider.filter_rows(local, &[&cell], &rows), Verdict::Holds),
        "reserved hole spelling classifies + conic-at-zero holds"
    );

    // Control: literal 42 is a malformed wire ref, never the hole —
    // outside the fragment, decided FALSE (not a refusal).
    let ops = body(42);
    let rows = CertRows::from_ops(&ops, [0xAB; 32], &deps);
    assert!(
        matches!(provider.filter_rows(local, &[&cell], &rows), Verdict::Fails),
        "non-reserved literal wire index is not the hole"
    );
}

/// The derived shapes of the claim relations the R4 fluid re-pin will
/// cite first — pinned (the fixtures are content-addressed, so these
/// are stable facts of the mint, and a derivation regression that
/// reshapes them fails here before any re-pin leg trips on it).
#[test]
fn qc_claim_shapes() {
    use qtsl_geolog_provider::{DomainSig, Ground, SortKey};
    let vocab = baked_vocab_from_container(qc_v1_container_bytes(), BAKED_QC_V1_REV).unwrap();
    // 165 at event 6 (was 150 at event 5/5.1): +17 new side
    // conditions — qcred_contains; the distance triple
    // (qtsl_couple_drift / qtsl_fixball / qtsl_dist_transport); the
    // verdict-stratum walks (qtsl_form_grounded, qtsl_init_bridge);
    // the event-rate lane (qtsl_rate_ub / qtsl_rate_lb /
    // qtsl_rate_clocks); the timed core (qtsl_tc_invrel /
    // qtsl_tc_firstservice / qtsl_tc_fssplit); the discharge kit
    // (verifiedCoverSplitValid, vcCellMemberForm, vcScopeBridgeForm);
    // and the lowbound renames' new spellings (qtsl_lowbound_boxes,
    // qtsl_hplate_lowbound) — MINUS 2: the floor-spelled pair those
    // renames retired. (The `e6_species_present` census below pins
    // the names one by one.)
    // 173 at event 7 (the timed-floor mint): +8 new side conditions —
    // the meter/lineage lane (qtsl_tr_meter, qtsl_unit_lineage,
    // qtsl_lineage_offset is rel-class and NOT counted here), the
    // node species walks (qtsl_palwayst_lineage, qtsl_palwayst_fold,
    // qtsl_rate_clock), the hplate lower-bound pair
    // (qtsl_hplate_coverage_lb, qtsl_hplate_flow_lb), and the support
    // warrant (qtsl_ksupport). Nothing retired. (The
    // `e7_species_present` census below pins the names one by one.)
    assert_eq!(vocab.claims.len(), 173, "qc side-condition roster size");
    let term = vocab.index.sort("Term").expect("Term sort");
    assert_eq!(term, (BAKED_QC_V1_REV, 14));
    // constExactEvalTrue {bowtie: Nat (the loader's view of `5 Index`),
    // l: Term, r: Term} — the fluid lane's shape, preserved by the bake.
    let d = vocab.index.fun("constExactEvalTrue").unwrap();
    assert_eq!(
        d.domain,
        DomainSig::Record(vec![
            ("bowtie".to_string(), SortKey::Ground(Ground::Nat)),
            ("l".to_string(), SortKey::Elem(term)),
            ("r".to_string(), SortKey::Elem(term)),
        ])
    );
    // TConst : Q -> Term.
    let t = vocab.index.fun("TConst").unwrap();
    assert_eq!(t.domain, DomainSig::Unary(SortKey::Ground(Ground::Q)));
    assert_eq!(t.codomain, Some(SortKey::Elem(term)));
    // qctCons {dom: Box, mode: Mode, tail, val: Poly} — the bake's
    // mode re-typing (pieces cite mode ENTITIES, never strings). The
    // geolog-beta qcert twin's entity-mode arm constructs exactly
    // this shape; this pin is the cross-repo tie.
    let mode_sort = vocab.index.sort("Mode").expect("Mode sort");
    let qct = vocab.index.fun("qctCons").expect("qctCons");
    let DomainSig::Record(fs) = &qct.domain else {
        panic!("qctCons is a record constructor")
    };
    let names: Vec<&str> = fs.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(names, ["dom", "mode", "tail", "val"]);
    assert_eq!(
        fs[1].1,
        SortKey::Elem(mode_sort),
        "mode field is Mode-typed"
    );
}

/// The event-6 species census — the name-level face of the
/// conformance discipline, for the six passenger families that have
/// NO provider family builder yet (the un-listed-family lesson: an
/// un-listed family's un-claiming is invisible to the family gate
/// below, so until a builder exists the presence of the VOCABULARY
/// itself is what this file can gate). A future revision silently
/// dropping one of these names fails here; a builder landing later
/// extends `assert_family_conformance` and may retire the matching
/// rows here.
#[test]
fn e6_species_present() {
    let vocab = baked_vocab_from_container(qc_v1_container_bytes(), BAKED_QC_V1_REV).unwrap();

    // Side-condition claims, one per new species walk (the +17 of
    // `qc_claim_shapes`' accounting).
    for name in [
        // verdict stratum
        "qcred_contains",
        "qtsl_form_grounded",
        "qtsl_init_bridge",
        // event-rate lane
        "qtsl_rate_ub",
        "qtsl_rate_lb",
        "qtsl_rate_clocks",
        // distance triple
        "qtsl_couple_drift",
        "qtsl_fixball",
        "qtsl_dist_transport",
        // timed core
        "qtsl_tc_invrel",
        "qtsl_tc_firstservice",
        "qtsl_tc_fssplit",
        // discharge kit
        "verifiedCoverSplitValid",
        "vcCellMemberForm",
        "vcScopeBridgeForm",
        // lowbound renames (new spellings)
        "qtsl_lowbound_boxes",
        "qtsl_hplate_lowbound",
    ] {
        let d = vocab
            .index
            .fun(name)
            .unwrap_or_else(|| panic!("event-6 closure declares `{name}`"));
        assert!(
            d.relational && d.side_condition,
            "`{name}` is a side condition"
        );
        assert!(vocab.claims.iter().any(|c| c == name), "{name} claimed");
    }
    // Derived relations that ride the same families (relational, NOT
    // side conditions — chase-derived, so never in the claim roster).
    for name in ["spec_consumes_trs", "qdist_symmetric", "qrfc_budget"] {
        let d = vocab.index.fun(name).expect("derived relation declared");
        assert!(d.relational && !d.side_condition, "{name} is derived");
        assert!(!vocab.claims.iter().any(|c| c == name));
    }
    // Entity/carrier sorts of the six families.
    for name in [
        "QForallSat",
        "QForallSatList",
        "QExistsEntry",
        "QExistsEntryList",
        "QVerdictForm",
        "QInitBridge",
        "QCoupleDrift",
        "QFixBall",
        "QDistTransport",
        "QDistEntry",
        "QDistSubject",
        "QDistBound",
        "QTimedSeq",
        "QInvRelativize",
        "QFirstService",
        "QFirstServiceSplit",
        "PHypMultiplier",
        "PVerifiedCover",
        "QRateUB",
        "QRateLB",
        "QRateFromClocks",
    ] {
        assert!(
            vocab.index.sort(name).is_some(),
            "event-6 closure declares sort `{name}`"
        );
    }
    // The event-rate formers and the properness twin.
    use qtsl_geolog_provider::DomainSig;
    let forall = vocab.index.sort("ForallSpec").expect("ForallSpec sort");
    for name in ["SRateLE", "SRateGE"] {
        let d = vocab.index.fun(name).expect("rate former declared");
        assert_eq!(
            d.codomain,
            Some(qtsl_geolog_provider::SortKey::Elem(forall))
        );
        let DomainSig::Record(fs) = &d.domain else {
            panic!("{name} is a record former")
        };
        let names: Vec<&str> = fs.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(names, ["rho", "sigma", "trs"], "{name} fields");
    }
    let exists = vocab.index.sort("ExistsSpec").expect("ExistsSpec sort");
    let sproper = vocab.index.fun("SProper").expect("SProper declared");
    assert_eq!(sproper.domain, DomainSig::Nullary);
    assert_eq!(
        sproper.codomain,
        Some(qtsl_geolog_provider::SortKey::Elem(exists))
    );
    // The face-typed verdict form (fields in bytewise wire order).
    let qvf = vocab.index.fun("qvfMk").expect("qvfMk declared");
    let DomainSig::Record(fs) = &qvf.domain else {
        panic!("qvfMk is a record former")
    };
    let names: Vec<&str> = fs.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(names, ["exists_face", "forall_face"], "qvfMk faces");
    // The unified warrant seam: 2-field entity shape, both routes.
    let qsat = vocab.index.sort("QSat").expect("QSat sort");
    let qfs = vocab.index.sort("QForallSat").expect("QForallSat sort");
    for name in ["qsat_warrant", "qsat_guard_warrant"] {
        let d = vocab.index.fun(name).expect("warrant relation");
        let DomainSig::Record(fs) = &d.domain else {
            panic!("{name} is a record relation")
        };
        let shape: Vec<(&str, _)> = fs.iter().map(|(n, k)| (n.as_str(), *k)).collect();
        assert_eq!(
            shape,
            vec![
                ("sat", qtsl_geolog_provider::SortKey::Elem(qsat)),
                ("warrant", qtsl_geolog_provider::SortKey::Elem(qfs)),
            ],
            "{name} is the event-6 entity shape"
        );
    }
    // Retired spellings are GONE (the rename is a rename, not an
    // alias): the floor-spelled relations and battery fields.
    for name in [
        "qtsl_floor_boxes",
        "qtsl_hplate_floor",
        "QSafetyBattery/floors",
        "QDeadlineBattery/floors",
        "QUntilBattery/avoid_floors",
        "QUntilBattery/target_floors",
        "QStreettBattery/floors",
        "QAvgBattery/floors",
    ] {
        assert!(
            vocab.index.fun(name).is_none(),
            "retired spelling `{name}` must not survive event 6"
        );
    }
    // Their lowbound replacements exist (battery fields are ordinary
    // valued funs, not claims).
    for name in [
        "QSafetyBattery/lowbounds",
        "QDeadlineBattery/lowbounds",
        "QUntilBattery/avoid_lowbounds",
        "QUntilBattery/target_lowbounds",
        "QStreettBattery/lowbounds",
        "QAvgBattery/lowbounds",
    ] {
        assert!(
            vocab.index.fun(name).is_some(),
            "lowbound spelling `{name}` declared"
        );
    }
    // The Q*Battery walk-relation GAP, pinned mechanically:
    // kind-typing and walk-demand axioms for the battery genus are
    // the rules-as-rows fan's material, deliberately absent at event
    // 6 (the theory's own SECTION K note) — only the Miranda battery
    // has a walk claim. The avgbattery provider family exists AHEAD
    // of its claim relation (its structural walk + loud deferral are
    // realized; nothing demands them yet). When the fan's mint lands
    // `qtsl_avg_battery`, this pin fails and the re-adjudication is
    // conscious: flip it to a presence + claim check, and grow the
    // deferral arm per the family module doc.
    assert!(
        vocab.index.fun("qtsl_avg_battery").is_none(),
        "`qtsl_avg_battery` is not yet minted at event 6 — if this fails, the \
         rules-as-rows fan has landed: re-adjudicate the avgbattery family's \
         claim status (see crate::avgbattery module doc)"
    );
    assert!(
        !vocab.claims.iter().any(|c| c == "qtsl_avg_battery"),
        "`qtsl_avg_battery` absent from the event-6 claim roster"
    );
}

/// The event-7 species census — the timed-floor mint's passenger
/// vocabulary, same genre as [`e6_species_present`]: no provider
/// family builder exists for these species yet, so the presence of
/// the VOCABULARY is what this file can gate; a builder landing later
/// extends `assert_family_conformance` and may retire matching rows
/// here.
#[test]
fn e7_species_present() {
    use qtsl_geolog_provider::DomainSig;
    let vocab = baked_vocab_from_container(qc_v1_container_bytes(), BAKED_QC_V1_REV).unwrap();

    // Side-condition claims — the +8 of `qc_claim_shapes`' accounting.
    for name in [
        // the meter/lineage lane
        "qtsl_tr_meter",
        "qtsl_unit_lineage",
        // the node species walks
        "qtsl_palwayst_lineage",
        "qtsl_palwayst_fold",
        "qtsl_rate_clock",
        // the hplate lower-bound pair
        "qtsl_hplate_coverage_lb",
        "qtsl_hplate_flow_lb",
        // the support warrant
        "qtsl_ksupport",
    ] {
        let d = vocab
            .index
            .fun(name)
            .unwrap_or_else(|| panic!("event-7 closure declares `{name}`"));
        assert!(
            d.relational && d.side_condition,
            "`{name}` is a side condition"
        );
        assert!(vocab.claims.iter().any(|c| c == name), "{name} claimed");
    }
    // Derived relations riding the same fragment (rel-class,
    // chase-derived, never in the claim roster).
    for name in ["qpatf_offsets", "qtsl_lineage_offset"] {
        let d = vocab.index.fun(name).expect("derived relation declared");
        assert!(d.relational && !d.side_condition, "{name} is derived");
        assert!(!vocab.claims.iter().any(|c| c == name));
    }
    // The node-species entity sorts + the support warrant carrier.
    for name in [
        "QPAlwaysTFromLineage",
        "QPAlwaysTFromFold",
        "QRateFromClock",
        "KSupportWarrant",
    ] {
        assert!(
            vocab.index.sort(name).is_some(),
            "event-7 closure declares sort `{name}`"
        );
    }
    // hrpDropAtMost joins HRowPolarity (the mint's one
    // mutation-shaped edit — the hrp_closed refusal's third
    // disjunct): a valued ctor whose codomain is the same
    // HRowPolarity carrier the incumbent pair targets.
    let drop = vocab
        .index
        .fun("hrpDropAtMost")
        .expect("hrpDropAtMost declared");
    let safety = vocab.index.fun("hrpSafety").expect("hrpSafety declared");
    assert!(!drop.relational, "hrpDropAtMost is a valued former");
    assert_eq!(
        drop.codomain, safety.codomain,
        "hrpDropAtMost targets the HRowPolarity carrier"
    );
    // The footprint row's upper-bound field (the lower-bound pair's
    // upper twin rides the same fragment).
    let ub = vocab
        .index
        .fun("HFootprintRow/ubound")
        .expect("HFootprintRow/ubound declared");
    assert!(
        matches!(ub.domain, DomainSig::Unary(_)),
        "ubound is a field"
    );
}

/// The family-resolution conformance gate over the REAL closures —
/// a recurring staleness hazard converted into a test-time gate.
///
/// Mechanism: every vocabulary build is itself a name-by-name check
/// that the theory still declares what the family reads; this
/// asserts the OUTCOME roster exactly, both directions, against the
/// derived production vocabulary. A theory revision that retires
/// vocabulary a family still reads (the syswire/carillon class:
/// `Manifest/transitions` et al. left at event-3 and two
/// families silently un-claimed while fixture-based tests stayed
/// green) fails HERE — and a family un-claiming that this list says
/// should claim names its reason via the vocabulary notes in the
/// panic message. Conversely, a by-design exemption becoming
/// resolvable (e.g. a fold moving staged-lane vocabulary into the
/// baked pair) also fails, so the exemption list is re-adjudicated
/// consciously rather than drifting.
fn assert_family_conformance(qv: &QtslVocab, expected_unclaimed: &[&str], closure: &str) {
    let families: &[(&str, bool)] = &[
        ("bl", qv.bl.is_some()),
        ("morse", qv.morse.is_some()),
        ("miranda", qv.miranda.is_some()),
        ("stochwire", qv.stochwire.is_some()),
        ("bagcanon", qv.bagcanon.is_some()),
        ("mask", qv.mask.is_some()),
        ("polycanon", qv.polycanon.is_some()),
        ("syswire", qv.syswire.is_some()),
        ("problog", qv.problog.is_some()),
        ("barycoord", qv.barycoord.is_some()),
        ("cellapp", qv.cellapp.is_some()),
        ("lattice", qv.lattice.is_some()),
        ("enclosure", qv.enclosure.is_some()),
        ("carillon", qv.carillon.is_some()),
        ("surgery", qv.surgery.is_some()),
        ("promise", qv.promise.is_some()),
        ("subdivide", qv.subdivide.is_some()),
        ("dtype", qv.dtype.is_some()),
        ("deadline", qv.deadline.is_some()),
        ("spdemoment", qv.spdemoment.is_some()),
        ("gymrw", qv.gymrw.is_some()),
        ("gymeproc", qv.gymeproc.is_some()),
        ("trwf", qv.trwf.is_some()),
        // Added at the provider revision: this family's
        // event-4 un-claiming had been invisible to the gate (the one
        // family missing from this list — the exact staleness class
        // the gate exists to catch).
        ("hplate", qv.hplate.is_some()),
        ("guard", qv.guard.is_some()),
        ("asel", qv.asel.is_some()),
        // Added at the event-5 provider port:
        // the drift-moment tie family — expected CLAIMED on both
        // closures from birth (QIntBoundFromSW rides the event-5 qc
        // AND dc revisions).
        ("swret", qv.swret.is_some()),
        // Added at the store-seam walk-evaluator port: the store-seam
        // pair. The KernelCite block and hnDigest/HypernetRef ride
        // the baked omnibus on both closures, so both families are
        // expected CLAIMED from birth (claims are vocabulary-gated —
        // a storeless deployment refuses per-instance, never
        // un-claims).
        ("circuit", qv.circuit.is_some()),
        ("gatescalar", qv.gatescalar.is_some()),
        // Added at the NN/semiring walk-evaluator port: the NN
        // conclusion-form family (hypernet ports + PrimApp/prim +
        // PReLU — deliberately NOT the cellapp group, whose
        // SimpC/nCells requirement keeps it exempt on the baked
        // closures) and the semiring-cell family (contract_semiring
        // + the five HAggKind constructors). Every name rides the
        // baked omnibus on BOTH closures (fun-index census taken at
        // that port), so both families are expected
        // CLAIMED from birth.
        ("nnform", qv.nnform.is_some()),
        ("contract", qv.contract.is_some()),
        // Added at the MarkFlow walk-evaluator port: the MarkFlow
        // family. The QWireComposeMarks block (node + carve/diagonal
        // spines + DiagKind genus) rides the baked omnibus on both
        // closures, so the family is expected CLAIMED from birth.
        ("markflow", qv.markflow.is_some()),
        // Added at the carved-window walk-evaluator port: the
        // carved-window pair. tkCarved/tr_dwell_gate and the
        // ScaleView/race vocabulary all ride the baked omnibus on
        // both closures, so both families are expected CLAIMED from
        // birth (claims are vocabulary-gated — a storeless deployment
        // refuses dwell-gate instances per-instance, never un-claims).
        ("dwellgate", qv.dwellgate.is_some()),
        ("ratecap", qv.ratecap.is_some()),
        // Added at the causality-walk evaluator port: the causality
        // walk family. The QWireCompose block is pre-existing
        // theory vocabulary (node attributes + the QNatList rank
        // spine + the wiring machinery), riding the baked omnibus
        // on both closures —
        // expected CLAIMED from birth.
        ("wirecausality", qv.wirecausality.is_some()),
        // Added at the LRA-battery walk port: the QAvgBattery
        // block (ten attributes at the e6 lowbounds spelling), the
        // SReturn/poAvg/oInd formers, and the spec record all ride
        // the baked omnibus on both closures — expected CLAIMED from
        // birth. The claim RELATION `qtsl_avg_battery` is NOT minted
        // at event 6 (see e6_species_present's gap pin): vocabulary
        // resolution and relation presence are independent, and this
        // row gates only the former.
        ("avgbattery", qv.avgbattery.is_some()),
    ];
    for (name, claimed) in families {
        let expected_claim = !expected_unclaimed.contains(name);
        assert_eq!(
            *claimed,
            expected_claim,
            "family `{name}` over the {closure} closure: expected \
             {} but it {} — if a theory revision changed the roster, \
             adjudicate and update the expected list (reasons in the \
             notes): {:#?}",
            if expected_claim {
                "claimed"
            } else {
                "not-claimed (documented exemption)"
            },
            if *claimed {
                "resolved"
            } else {
                "did not resolve"
            },
            qv.notes
        );
    }
}

/// The active exemption rosters (event 4 — the per-event const
/// selection died with the legacy tier, greenfield ruling 2026-07-29
/// 14:28: the rosters track the primary event directly, and a mint
/// swap edits them in the same motion as the pins). Each entry's
/// adjudicated reason rides its comment; the gate refuses a roster
/// drifting in either direction.
const QC_UNCLAIMED: &[&str] = &[
    // `SimpC/nCells` lives in the certificate EXTENSION revision, not
    // the baked tower (the theory's own comment beside FarkasPairCert).
    "cellapp",
    // The float lane wants the structured Dtype record; the baked
    // Dtypes theory is a CLOSED ENUM (open adjudication: the
    // structured vocabulary may belong to the mtk normalized stack).
    "dtype",
    // Needs a kernel row species; the qc closure carries no Dtmc
    // theory. (The event-4 spelling reads were re-keyed dual-shape at
    // the provider revision — the kernel species is the
    // one remaining resolvent, so qc alone stays exempt.)
    "deadline",
    // Staged-lane chain vocabulary (QSpdeSpec / GymRwCert /
    // QEprocCert) — absent from the baked pair by design.
    "spdemoment",
    "gymrw",
    "gymeproc",
    // (morse re-claimed at the provider revision: the
    // atom decode is dual-shape — oPoly hop post-grid, direct poly on
    // legacy closures.)
];
const DC_UNCLAIMED: &[&str] = &[
    "cellapp",
    "dtype",
    // (deadline re-claimed on dc at the provider
    // revision: dual-shape spec spelling + the atoms' oPoly hop.)
    "spdemoment",
    "gymrw",
    "gymeproc",
];

/// The gate over the qc chain (10 theories: the baked pair).
#[test]
fn qc_family_conformance() {
    let vocab = baked_vocab_from_container(qc_v1_container_bytes(), BAKED_QC_V1_REV)
        .expect("qc chain derives");
    let qv = QtslVocab::build(&[&vocab.index]);
    assert_family_conformance(&qv, QC_UNCLAIMED, "qc");
}

/// The gate over the dc chain (11 theories: qc + Dtmc).
#[test]
fn dc_family_conformance() {
    let vocab = baked_vocab_from_container(dc_v1_container_bytes(), BAKED_DC_V1_REV)
        .expect("dc chain derives");
    let qv = QtslVocab::build(&[&vocab.index]);
    assert_family_conformance(&qv, DC_UNCLAIMED, "dc");
}

/// The asel OPTIONAL compiled-form group resolves on BOTH baked
/// closures. Family claiming alone does not imply it (every member
/// failure is erased to `None` at resolution), so a theory revision
/// reshaping e.g. `qfsCons` or `qsat_zeno_budget` would otherwise
/// leave this suite green while every production `qtsl_asel_attach`
/// instance refused "vocabulary absent" at runtime.
#[test]
fn asel_compiled_form_group_resolves_on_baked_closures() {
    for (bytes, rev, closure) in [
        (qc_v1_container_bytes(), BAKED_QC_V1_REV, "qc"),
        (dc_v1_container_bytes(), BAKED_DC_V1_REV, "dc"),
    ] {
        let vocab = baked_vocab_from_container(bytes, rev)
            .unwrap_or_else(|e| panic!("{closure} chain derives: {e:?}"));
        let qv = QtslVocab::build(&[&vocab.index]);
        let asel = qv
            .asel
            .as_ref()
            .unwrap_or_else(|| panic!("asel claims on {closure}"));
        assert!(
            asel.compiled_resolved(),
            "the event-6 compiled-form group resolves on {closure}"
        );
    }
}

// ── the dual-pin roster (primary pair + legacy generations) ─────────

/// The primary pair leads the roster, in qc/dc order, at the primary
/// event, byte-tied to the V1 aliases (which the pins-file tie above
/// binds to the committed pins record — so a half-done mint swap that
/// re-aims the aliases without the roster, or vice versa, fails
/// here).
#[test]
fn roster_leads_with_the_primary_pair() {
    assert!(BAKED_ROSTER.len() >= 2, "roster carries the primary pair");
    let (q, d) = (&BAKED_ROSTER[0], &BAKED_ROSTER[1]);
    assert_eq!(
        (q.closure, q.event, q.rev),
        ("qc", BAKED_PRIMARY_EVENT, BAKED_QC_V1_REV)
    );
    assert_eq!(
        (d.closure, d.event, d.rev),
        ("dc", BAKED_PRIMARY_EVENT, BAKED_DC_V1_REV)
    );
    assert!(q.is_primary() && d.is_primary());
    // The containers are the primary containers, byte-identical.
    assert_eq!((q.container)(), qc_v1_container_bytes());
    assert_eq!((d.container)(), dc_v1_container_bytes());
    // Every non-leading row is a LEGACY row: a strictly older event.
    for p in &BAKED_ROSTER[2..] {
        assert!(
            p.event < BAKED_PRIMARY_EVENT && !p.is_primary(),
            "roster tail row (event {}, {}) is not legacy — the swap \
             appended above the line, or forgot to bump BAKED_PRIMARY_EVENT",
            p.event,
            p.closure
        );
    }
}

/// Roster revisions are pairwise distinct — the swap-integrity
/// witness: a botched mint swap that re-aims one primary alias but
/// not the other (leaving it equal to the freshly-appended legacy
/// entry) fails here rather than silently double-listing a rev.
#[test]
fn roster_revs_pairwise_distinct() {
    for (i, a) in BAKED_ROSTER.iter().enumerate() {
        for b in &BAKED_ROSTER[i + 1..] {
            assert_ne!(
                a.rev, b.rev,
                "duplicate revision in the roster: event {} {} vs event {} {}",
                a.event, a.closure, b.event, b.closure
            );
        }
    }
}

/// Each roster row's container actually carries its pinned revision
/// and derives (the row-level version of the qc/dc round-trips above,
/// quantified over the whole roster so appended legacy rows are
/// covered by construction, not by remembering to add a test).
#[test]
fn every_roster_row_derives_from_its_own_container() {
    for p in BAKED_ROSTER {
        let vocab = baked_vocab_from_container((p.container)(), p.rev).unwrap_or_else(|e| {
            panic!(
                "roster row event {} {} does not derive from its container: {e}",
                p.event, p.closure
            )
        });
        assert_eq!(vocab.revision, p.rev);
    }
}

/// Unknown revisions resolve to nothing (the classify gate's refusal
/// path), and the primary revisions resolve to the primary rows.
#[test]
fn resolve_finds_primary_and_refuses_unknown() {
    let q = resolve_baked_rev(&BAKED_QC_V1_REV).expect("primary qc resolves");
    assert!(q.is_primary() && q.closure == "qc");
    assert!(resolve_baked_rev(&[0x77; 32]).is_none());
}

/// The committed mutant probe: a roster row whose pinned chid has one
/// corrupted byte REFUSES at derivation (chain_missing — the container
/// carries no commit at the corrupt chid), never yielding a vocabulary
/// under the wrong pin. Dispatch integrity is content-addressed all
/// the way down, so a roster typo cannot silently serve the wrong
/// vocabulary. (Ran against the legacy tier before the greenfield cut;
/// the primary pair carries the same property.)
#[test]
fn corrupted_roster_chid_refuses_at_derivation() {
    let mut bad_rev = BAKED_QC_V1_REV;
    bad_rev[7] ^= 0x01;
    let corrupt = BakedPin {
        event: BAKED_PRIMARY_EVENT,
        closure: "qc",
        rev: bad_rev,
        container: qc_v1_container_bytes,
    };
    let err = baked_vocab_from_container((corrupt.container)(), corrupt.rev)
        .expect_err("a corrupted roster chid must refuse");
    assert!(
        err.contains("chain_missing_revision"),
        "refusal names the missing revision: {err}"
    );
}
