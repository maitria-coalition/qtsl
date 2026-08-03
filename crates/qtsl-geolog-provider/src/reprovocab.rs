//! Pinned reproduction vocabularies: declaration indices for sealed
//! certificate artifacts.
//!
//! A sealed certificate container (`.glc`) references its vocabulary
//! by revision chid; producer and checker must agree on the declared
//! shapes AND the counter assignment behind those chids. Each
//! function here is one such pinned contract: a [`TheoryIndex`] whose
//! revision identifier and insertion order are frozen — a change is a
//! new versioned vocabulary, never an edit (artifacts in the wild dep
//! the old chids forever).
//!
//! [`fluid_v0`] is the QTSL certificate-fragment vocabulary used by
//! the fluid-network drift certificates: the Term/Formula/Judgment
//! constructor families, the combination and PSD certificate nodes,
//! the simplex membership chain (shapes transcribed from the theory
//! source, record fields in bytewise order — the wire argument
//! order), plus the four side-condition relations the certificates
//! claim (`farkasCombinationValid`, `constExactEvalTrue`,
//! `syzygyCombinationValid`, `syzygyConclusionFormRel`). Its revision
//! identifier is the constant byte pattern `0x5F × 32` — a pinned
//! synthetic revision (declaration data as contract); moving these
//! declarations onto staged theory commits, with the index derived
//! from decoded declaration rows, is the planned successor and will
//! arrive as a NEW vocabulary version.

use crate::theory::{Chid, DomainSig, FunDecl, Ground, SortKey, TheoryIndex};

/// The baked-pair vocabulary, version 1 (derived, not transcribed):
/// declaration indices computed from the minted qc/dc revisions'
/// decoded declaration rows — the successor the module docs above
/// promised. See its module docs for the pin/derivation split.
pub mod baked;

/// The BL supermartingale reproduction vocabulary (staged-chid
/// pins). See its module docs for the trust posture delta from
/// [`fluid_v0`]'s synthetic revision.
pub mod bl;

/// The gym deadline-table reproduction vocabulary (staged-chid pins:
/// the Qtsl/QtslCert/Dtmc revisions). See its module docs for the
/// cross-repo pin discipline.
pub mod gym;

/// Revision identifier of the v0 fluid reproduction vocabulary.
pub const FLUID_V0_REV: [u8; 32] = [0x5F; 32];

fn record(fields: &[(&str, SortKey)]) -> DomainSig {
    DomainSig::Record(fields.iter().map(|(n, s)| (n.to_string(), *s)).collect())
}

/// The v0 fluid reproduction vocabulary (module docs). Deterministic:
/// every call constructs the identical index.
pub fn fluid_v0() -> TheoryIndex {
    let mut ix = TheoryIndex::new(FLUID_V0_REV);
    let mut ctr: u32 = 0;
    let mut next = || {
        ctr += 1;
        ctr
    };
    let term = ix.insert_sort("Term", next());
    let formula = ix.insert_sort("Formula", next());
    let wire = ix.insert_sort("Wire", next());
    let judgment = ix.insert_sort("Judgment", next());
    let proof = ix.insert_sort("Proof", next());
    let psyzygy = ix.insert_sort("PSyzygy", next());
    let pbound = ix.insert_sort("PBound", next());
    let psd_t = ix.insert_sort("PPsdCertT", next());
    let psd_dd = ix.insert_sort("PPsdCertDD", next());
    let psd_k = ix.insert_sort("PPsdCertK", next());
    let tensor_type = ix.insert_sort("TensorType", next());
    let shape = ix.insert_sort("Shape", next());
    let dtype = ix.insert_sort("Dtype", next());
    let simplex = ix.insert_sort("Simplex", next());
    let ext_set = ix.insert_sort("ExtensionSet", next());

    let e = SortKey::Elem;
    let g = SortKey::Ground;
    let mut fun = |name: &str, domain: DomainSig, codomain: SortKey| {
        ix.insert_fun(FunDecl {
            name: name.to_string(),
            chid: (FLUID_V0_REV, next()),
            relational: false,
            side_condition: false,
            domain,
            codomain: Some(codomain),
        });
    };
    let pair = |s: Chid| record(&[("l", e(s)), ("r", e(s))]);

    // Term constructors.
    fun("TVar", DomainSig::Unary(e(wire)), e(term));
    fun("TConst", DomainSig::Unary(g(Ground::Q)), e(term));
    fun("TAdd", pair(term), e(term));
    fun("TMul", pair(term), e(term));
    fun("TSub", pair(term), e(term));
    fun("TNeg", DomainSig::Unary(e(term)), e(term));
    fun(
        "TIdx",
        record(&[("i", g(Ground::Nat)), ("t", e(term))]),
        e(term),
    );
    fun("THole", DomainSig::Nullary, e(term));

    // Formula constructors.
    for name in [
        "FAtomLT", "FAtomLE", "FAtomEQ", "FAtomGE", "FAtomGT", "FAtomNE",
    ] {
        fun(name, pair(term), e(formula));
    }
    fun("FAnd", pair(formula), e(formula));
    fun("FOr", pair(formula), e(formula));
    fun("FTrue", DomainSig::Nullary, e(formula));
    fun("FFalse", DomainSig::Nullary, e(formula));
    fun("FSpH", DomainSig::Nullary, e(formula));
    fun(
        "FInRegion",
        record(&[("S", e(ext_set)), ("simplex", e(simplex)), ("t", e(term))]),
        e(formula),
    );

    // Judgement / proof / wire typing.
    fun("Judgment/pre", DomainSig::Unary(e(judgment)), e(formula));
    fun("Judgment/post", DomainSig::Unary(e(judgment)), e(formula));
    fun("Proof/concludes", DomainSig::Unary(e(proof)), e(judgment));
    fun("Wire/type", DomainSig::Unary(e(wire)), e(tensor_type));
    fun(
        "mkTensorType",
        record(&[("dtype", e(dtype)), ("shape", e(shape))]),
        e(tensor_type),
    );
    fun("empty", DomainSig::Nullary, e(shape));
    fun(
        "cons",
        record(&[("head", g(Ground::Nat)), ("tail", e(shape))]),
        e(shape),
    );

    // Combination nodes (PSyzygy and its alias PBound).
    for (prefix, node) in [("PSyzygy", psyzygy), ("PBound", pbound)] {
        let f = |field: &str| format!("{prefix}/{field}");
        fun(&f("proof"), DomainSig::Unary(e(node)), e(proof));
        fun(&f("nComponents"), DomainSig::Unary(e(node)), g(Ground::Nat));
        fun(
            &f("component"),
            record(&[("k", g(Ground::Nat)), ("p", e(node))]),
            e(proof),
        );
        fun(&f("combinationCoeffs"), DomainSig::Unary(e(node)), e(term));
        fun(&f("conclusion"), DomainSig::Unary(e(node)), e(term));
    }

    // PSD certificate nodes (carried for full-family resolution).
    for (prefix, node) in [("PPsdCertT", psd_t), ("PPsdCertDD", psd_dd)] {
        let f = |field: &str| format!("{prefix}/{field}");
        fun(&f("n"), DomainSig::Unary(e(node)), g(Ground::Nat));
        fun(
            &f("A"),
            DomainSig::Unary(e(node)),
            SortKey::TensorOf(Ground::Q),
        );
        fun(
            &f("Z"),
            DomainSig::Unary(e(node)),
            SortKey::TensorOf(Ground::Q),
        );
        fun(
            &f("term"),
            record(&[("i", g(Ground::Nat)), ("p", e(node))]),
            e(term),
        );
        fun(&f("conclusion"), DomainSig::Unary(e(node)), e(term));
    }
    {
        let f = |field: &str| format!("PPsdCertK/{field}");
        for field in ["m", "k", "nTotal", "innerT"] {
            fun(&f(field), DomainSig::Unary(e(psd_k)), g(Ground::Nat));
        }
        for field in ["A", "N", "B", "Z"] {
            fun(
                &f(field),
                DomainSig::Unary(e(psd_k)),
                SortKey::TensorOf(Ground::Q),
            );
        }
        fun(
            &f("term"),
            record(&[("i", g(Ground::Nat)), ("p", e(psd_k))]),
            e(term),
        );
        fun(&f("conclusion"), DomainSig::Unary(e(psd_k)), e(term));
    }

    // The mask family's resolution chain + membership relations.
    {
        let simpc = ix.insert_sort("SimpC", next());
        let mut plain = |name: &str, domain: DomainSig, codomain: SortKey| {
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (FLUID_V0_REV, next()),
                relational: false,
                side_condition: false,
                domain,
                codomain: Some(codomain),
            });
        };
        plain(
            "SimpC/n_vertices",
            DomainSig::Unary(e(simpc)),
            g(Ground::Nat),
        );
        plain("Simplex/complex", DomainSig::Unary(e(simplex)), e(simpc));
        plain(
            "ExtensionSet/simplex",
            DomainSig::Unary(e(ext_set)),
            e(simplex),
        );
        let mut rel = |name: &str, domain: DomainSig| {
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (FLUID_V0_REV, next()),
                relational: true,
                side_condition: false,
                domain,
                codomain: None,
            });
        };
        rel(
            "Simplex/contains",
            record(&[("s", e(simplex)), ("v", g(Ground::Nat))]),
        );
        rel(
            "ExtensionSet/contains",
            record(&[("S", e(ext_set)), ("v", g(Ground::Nat))]),
        );
    }

    // Side-condition relations the certificates CLAIM as rows (the
    // checker discharges each claim through the ground provider).
    // Record fields in bytewise order — the wire argument order.
    {
        let mut side = |name: &str, domain: DomainSig| {
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (FLUID_V0_REV, next()),
                relational: true,
                side_condition: true,
                domain,
                codomain: None,
            });
        };
        side(
            "farkasCombinationValid",
            record(&[
                ("combinationCoeffs", e(term)),
                ("conclusion", e(term)),
                ("premise", e(formula)),
            ]),
        );
        side(
            "constExactEvalTrue",
            record(&[("bowtie", g(Ground::Nat)), ("l", e(term)), ("r", e(term))]),
        );
        side("syzygyCombinationValid", DomainSig::Unary(e(psyzygy)));
        side(
            "syzygyConclusionFormRel",
            record(&[("conclusion", e(term)), ("formula", e(formula))]),
        );
    }
    ix
}

/// The four claim-relation names of [`fluid_v0`], in dispatch report
/// order.
pub const FLUID_V0_CLAIMS: [&str; 4] = [
    "farkasCombinationValid",
    "constExactEvalTrue",
    "syzygyCombinationValid",
    "syzygyConclusionFormRel",
];

/// Revision identifier of the v0 SPDE moment-core reproduction
/// vocabulary. Self-documenting ASCII (28 bytes + 4 NULs) rather than
/// a repeated-byte pattern — vocabulary revisions must never collide,
/// and a name collides with nothing.
pub const SPDE_V0_REV: [u8; 32] = *b"maitria-spde-moment-vocab-v0\0\0\0\0";

/// The v0 SPDE moment-core reproduction vocabulary: the
/// stochastic-heat / stochastic-Burgers moment certificates at rungs
/// SW-m + S1 (expected-energy claims with the Itô-correction beta
/// discipline, tier-(ii)/(iii) non-degeneracy witnesses, and the
/// two-sided summed-floor enclosures whose floor tie is the family's
/// falsifier). Primary data lives in rows — the noise spectrum
/// (drivers + constructor-required tail form), the claims, the
/// witness trajectories — and the checker recomputes everything else
/// (rates, mode floors, exponential brackets) from them: derived
/// quantities are never stored, so forging one is unrepresentable.
///
/// Deterministic: every call constructs the identical index. Same
/// versioning law as [`fluid_v0`]: a change is a NEW vocabulary,
/// never an edit.
pub fn spde_v0() -> TheoryIndex {
    let mut ix = TheoryIndex::new(SPDE_V0_REV);
    let mut ctr: u32 = 0;
    let mut next = || {
        ctr += 1;
        ctr
    };
    let spec = ix.insert_sort("QSpdeSpec", next());
    let tailform = ix.insert_sort("QTailForm", next());
    let dlist = ix.insert_sort("QDriverList", next());
    let driver = ix.insert_sort("QDriver", next());
    let corr = ix.insert_sort("QItoCorr", next());
    let claim = ix.insert_sort("QSpdeClaim", next());
    let sample = ix.insert_sort("QTrajSample", next());
    let slist = ix.insert_sort("QTrajSampleList", next());
    let mtraj = ix.insert_sort("QModeTraj", next());
    let mlist = ix.insert_sort("QModeTrajList", next());
    let tier = ix.insert_sort("QTierWit", next());
    let tmrow = ix.insert_sort("QTimeModeRow", next());
    let tmlist = ix.insert_sort("QTimeModeList", next());
    let trow = ix.insert_sort("QTimeRow", next());
    let trlist = ix.insert_sort("QTimeRowList", next());
    let sfloor = ix.insert_sort("QSummedFloor", next());

    let e = SortKey::Elem;
    let g = SortKey::Ground;
    let mut fun = |name: &str, domain: DomainSig, codomain: SortKey| {
        ix.insert_fun(FunDecl {
            name: name.to_string(),
            chid: (SPDE_V0_REV, next()),
            relational: false,
            side_condition: false,
            domain,
            codomain: Some(codomain),
        });
    };

    // The spectrum: nu + finite rank + driver rows + a REQUIRED tail
    // form (constructor-required in the staged theory; here a field
    // row whose ABSENCE the evaluator refuses — never reads as zero).
    fun("QSpdeSpec/drivers", DomainSig::Unary(e(spec)), e(dlist));
    fun("QSpdeSpec/nu", DomainSig::Unary(e(spec)), g(Ground::Q));
    fun("QSpdeSpec/rank", DomainSig::Unary(e(spec)), g(Ground::Nat));
    fun("QSpdeSpec/tail", DomainSig::Unary(e(spec)), e(tailform));
    fun("tfZero", DomainSig::Nullary, e(tailform));
    fun(
        "tfBracket",
        record(&[("hi", g(Ground::Q)), ("lo", g(Ground::Q))]),
        e(tailform),
    );
    fun("tfDivergent", DomainSig::Nullary, e(tailform));
    fun("qdlNil", DomainSig::Nullary, e(dlist));
    fun(
        "qdlCons",
        record(&[("head", e(driver)), ("tail", e(dlist))]),
        e(dlist),
    );
    fun("QDriver/k", DomainSig::Unary(e(driver)), g(Ground::Nat));
    fun("QDriver/q", DomainSig::Unary(e(driver)), g(Ground::Q));

    // The Itô correction: value = (1/2) · hess · tr(Q), trace
    // recomputed from the spec's driver rows at every discharge.
    fun("QItoCorr/hess", DomainSig::Unary(e(corr)), g(Ground::Q));
    fun("QItoCorr/spec", DomainSig::Unary(e(corr)), e(spec));
    fun("QItoCorr/value", DomainSig::Unary(e(corr)), g(Ground::Q));

    // The moment claims (alpha = 0 and alpha = 2·nu in the landed
    // instances; floor row present iff alpha > 0).
    fun("QSpdeClaim/alpha", DomainSig::Unary(e(claim)), g(Ground::Q));
    fun("QSpdeClaim/beta", DomainSig::Unary(e(claim)), g(Ground::Q));
    fun(
        "QSpdeClaim/betaJet",
        DomainSig::Unary(e(claim)),
        g(Ground::Q),
    );
    fun("QSpdeClaim/corr", DomainSig::Unary(e(claim)), e(corr));
    fun("QSpdeClaim/floor", DomainSig::Unary(e(claim)), g(Ground::Q));

    // Tier-(ii) trajectories: per-sample declared enclosures against
    // recomputed alternating exp brackets; rates and mode floors are
    // derived from the spec, never declared.
    fun("QTrajSample/mhi", DomainSig::Unary(e(sample)), g(Ground::Q));
    fun("QTrajSample/mlo", DomainSig::Unary(e(sample)), g(Ground::Q));
    fun(
        "QTrajSample/nhi",
        DomainSig::Unary(e(sample)),
        g(Ground::Nat),
    );
    fun(
        "QTrajSample/nlo",
        DomainSig::Unary(e(sample)),
        g(Ground::Nat),
    );
    fun("QTrajSample/t", DomainSig::Unary(e(sample)), g(Ground::Q));
    fun("qtsNil", DomainSig::Nullary, e(slist));
    fun(
        "qtsCons",
        record(&[("head", e(sample)), ("tail", e(slist))]),
        e(slist),
    );
    fun("QModeTraj/k", DomainSig::Unary(e(mtraj)), g(Ground::Nat));
    fun("QModeTraj/samples", DomainSig::Unary(e(mtraj)), e(slist));
    fun("qmtNil", DomainSig::Nullary, e(mlist));
    fun(
        "qmtCons",
        record(&[("head", e(mtraj)), ("tail", e(mlist))]),
        e(mlist),
    );
    fun("QTierWit/claim", DomainSig::Unary(e(tier)), e(claim));
    fun("QTierWit/fraction", DomainSig::Unary(e(tier)), g(Ground::Q));
    fun("QTierWit/modes", DomainSig::Unary(e(tier)), e(mlist));
    fun(
        "QTierWit/partialFloor",
        DomainSig::Unary(e(tier)),
        g(Ground::Q),
    );
    fun("QTierWit/sumLo", DomainSig::Unary(e(tier)), g(Ground::Q));

    // S1 summed-floor enclosures: powered brackets at canonical
    // minimal power, common times, confinement + width + attainment,
    // and the floor tie F + deficit = claim.floor (the falsifier).
    fun("QTimeModeRow/k", DomainSig::Unary(e(tmrow)), g(Ground::Nat));
    fun("QTimeModeRow/mhi", DomainSig::Unary(e(tmrow)), g(Ground::Q));
    fun("QTimeModeRow/mlo", DomainSig::Unary(e(tmrow)), g(Ground::Q));
    fun(
        "QTimeModeRow/nhi",
        DomainSig::Unary(e(tmrow)),
        g(Ground::Nat),
    );
    fun(
        "QTimeModeRow/nlo",
        DomainSig::Unary(e(tmrow)),
        g(Ground::Nat),
    );
    fun(
        "QTimeModeRow/power",
        DomainSig::Unary(e(tmrow)),
        g(Ground::Nat),
    );
    fun("qtmNil", DomainSig::Nullary, e(tmlist));
    fun(
        "qtmCons",
        record(&[("head", e(tmrow)), ("tail", e(tmlist))]),
        e(tmlist),
    );
    fun("QTimeRow/modes", DomainSig::Unary(e(trow)), e(tmlist));
    fun("QTimeRow/sumHi", DomainSig::Unary(e(trow)), g(Ground::Q));
    fun("QTimeRow/sumLo", DomainSig::Unary(e(trow)), g(Ground::Q));
    fun("QTimeRow/t", DomainSig::Unary(e(trow)), g(Ground::Q));
    fun("qtrNil", DomainSig::Nullary, e(trlist));
    fun(
        "qtrCons",
        record(&[("head", e(trow)), ("tail", e(trlist))]),
        e(trlist),
    );
    fun(
        "QSummedFloor/attainFraction",
        DomainSig::Unary(e(sfloor)),
        g(Ground::Q),
    );
    fun("QSummedFloor/claim", DomainSig::Unary(e(sfloor)), e(claim));
    fun(
        "QSummedFloor/deficit",
        DomainSig::Unary(e(sfloor)),
        g(Ground::Q),
    );
    fun(
        "QSummedFloor/fexact",
        DomainSig::Unary(e(sfloor)),
        g(Ground::Q),
    );
    fun("QSummedFloor/times", DomainSig::Unary(e(sfloor)), e(trlist));
    fun(
        "QSummedFloor/widthBound",
        DomainSig::Unary(e(sfloor)),
        g(Ground::Q),
    );

    // The three claim relations (side conditions the checker
    // discharges through the ground provider).
    {
        let mut side = |name: &str, domain: DomainSig| {
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (SPDE_V0_REV, next()),
                relational: true,
                side_condition: true,
                domain,
                codomain: None,
            });
        };
        side("spdeClaimValid", DomainSig::Unary(e(claim)));
        side("spdeTierWitnessValid", DomainSig::Unary(e(tier)));
        side("spdeSummedFloorValid", DomainSig::Unary(e(sfloor)));
    }
    ix
}

/// The three claim-relation names of [`spde_v0`], in dispatch report
/// order.
pub const SPDE_V0_CLAIMS: [&str; 3] = [
    "spdeClaimValid",
    "spdeTierWitnessValid",
    "spdeSummedFloorValid",
];

/// Revision identifier of the v0 Petri P-invariant reproduction
/// vocabulary (same self-documenting-ASCII convention as
/// [`SPDE_V0_REV`]).
pub const PETRI_V0_REV: [u8; 32] = *b"maitria-petri-invar-vocab-v0\0\0\0\0";

/// The v0 Petri P-invariant reproduction vocabulary: the
/// MCC P/T-net witness battery's certificates as sealed containers.
///
/// A certificate carries PRIMARY DATA ONLY — one `PNet` element with
/// its dimensions and sparse flow/marking rows, plus `PInv` elements
/// (the proposed invariant vectors: sparse coefficient rows and the
/// stated initial charge). No term trees and no claim rows are stored:
/// the checker constructs every `constExactEvalTrue` obligation itself
/// from the net rows — per invariant `y`, per transition `t`, the
/// conservation identity `Σ_p y_p·(post[p,t] − pre[p,t]) = 0`, and one
/// initial-charge identity `Σ_p y_p·m0_p = b` — so a stored-tree
/// forgery is unrepresentable rather than discouraged (the F5
/// recompute-from-primary discipline made total).
///
/// The Term/Formula/…/mask families are carried verbatim from the
/// witness battery's synthetic stack (shapes transcribed from the
/// theory source): the BL family group must resolve for
/// `constExactEvalTrue` to be claimed by the provider, and the checker
/// emits its constructed term trees against these declarations. NONE
/// of the four fluid claim relations are declared here — a Petri
/// certificate has no lawful claim row.
///
/// Deterministic: every call constructs the identical index. Same
/// versioning law as [`fluid_v0`]: a change is a NEW vocabulary,
/// never an edit.
pub fn petri_v0() -> TheoryIndex {
    let mut ix = TheoryIndex::new(PETRI_V0_REV);
    let mut ctr: u32 = 0;
    let mut next = || {
        ctr += 1;
        ctr
    };
    let term = ix.insert_sort("Term", next());
    let formula = ix.insert_sort("Formula", next());
    let wire = ix.insert_sort("Wire", next());
    let judgment = ix.insert_sort("Judgment", next());
    let proof = ix.insert_sort("Proof", next());
    let psyzygy = ix.insert_sort("PSyzygy", next());
    let pbound = ix.insert_sort("PBound", next());
    let psd_t = ix.insert_sort("PPsdCertT", next());
    let psd_dd = ix.insert_sort("PPsdCertDD", next());
    let psd_k = ix.insert_sort("PPsdCertK", next());
    let tensor_type = ix.insert_sort("TensorType", next());
    let shape = ix.insert_sort("Shape", next());
    let dtype = ix.insert_sort("Dtype", next());
    let simplex = ix.insert_sort("Simplex", next());
    let ext_set = ix.insert_sort("ExtensionSet", next());

    let e = SortKey::Elem;
    let g = SortKey::Ground;
    let mut fun = |name: &str, domain: DomainSig, codomain: SortKey| {
        ix.insert_fun(FunDecl {
            name: name.to_string(),
            chid: (PETRI_V0_REV, next()),
            relational: false,
            side_condition: false,
            domain,
            codomain: Some(codomain),
        });
    };
    let pair = |s: Chid| record(&[("l", e(s)), ("r", e(s))]);

    // Term constructors.
    fun("TVar", DomainSig::Unary(e(wire)), e(term));
    fun("TConst", DomainSig::Unary(g(Ground::Q)), e(term));
    fun("TAdd", pair(term), e(term));
    fun("TMul", pair(term), e(term));
    fun("TSub", pair(term), e(term));
    fun("TNeg", DomainSig::Unary(e(term)), e(term));
    fun(
        "TIdx",
        record(&[("i", g(Ground::Nat)), ("t", e(term))]),
        e(term),
    );
    fun("THole", DomainSig::Nullary, e(term));

    // Formula constructors.
    for name in [
        "FAtomLT", "FAtomLE", "FAtomEQ", "FAtomGE", "FAtomGT", "FAtomNE",
    ] {
        fun(name, pair(term), e(formula));
    }
    fun("FAnd", pair(formula), e(formula));
    fun("FOr", pair(formula), e(formula));
    fun("FTrue", DomainSig::Nullary, e(formula));
    fun("FFalse", DomainSig::Nullary, e(formula));
    fun("FSpH", DomainSig::Nullary, e(formula));
    fun(
        "FInRegion",
        record(&[("S", e(ext_set)), ("simplex", e(simplex)), ("t", e(term))]),
        e(formula),
    );

    // Judgement / proof / wire typing.
    fun("Judgment/pre", DomainSig::Unary(e(judgment)), e(formula));
    fun("Judgment/post", DomainSig::Unary(e(judgment)), e(formula));
    fun("Proof/concludes", DomainSig::Unary(e(proof)), e(judgment));
    fun("Wire/type", DomainSig::Unary(e(wire)), e(tensor_type));
    fun(
        "mkTensorType",
        record(&[("dtype", e(dtype)), ("shape", e(shape))]),
        e(tensor_type),
    );
    fun("empty", DomainSig::Nullary, e(shape));
    fun(
        "cons",
        record(&[("head", g(Ground::Nat)), ("tail", e(shape))]),
        e(shape),
    );

    // Combination nodes (PSyzygy and its alias PBound).
    for (prefix, node) in [("PSyzygy", psyzygy), ("PBound", pbound)] {
        let f = |field: &str| format!("{prefix}/{field}");
        fun(&f("proof"), DomainSig::Unary(e(node)), e(proof));
        fun(&f("nComponents"), DomainSig::Unary(e(node)), g(Ground::Nat));
        fun(
            &f("component"),
            record(&[("k", g(Ground::Nat)), ("p", e(node))]),
            e(proof),
        );
        fun(&f("combinationCoeffs"), DomainSig::Unary(e(node)), e(term));
        fun(&f("conclusion"), DomainSig::Unary(e(node)), e(term));
    }

    // PSD certificate nodes (carried for full-family resolution).
    for (prefix, node) in [("PPsdCertT", psd_t), ("PPsdCertDD", psd_dd)] {
        let f = |field: &str| format!("{prefix}/{field}");
        fun(&f("n"), DomainSig::Unary(e(node)), g(Ground::Nat));
        fun(
            &f("A"),
            DomainSig::Unary(e(node)),
            SortKey::TensorOf(Ground::Q),
        );
        fun(
            &f("Z"),
            DomainSig::Unary(e(node)),
            SortKey::TensorOf(Ground::Q),
        );
        fun(
            &f("term"),
            record(&[("i", g(Ground::Nat)), ("p", e(node))]),
            e(term),
        );
        fun(&f("conclusion"), DomainSig::Unary(e(node)), e(term));
    }
    {
        let f = |field: &str| format!("PPsdCertK/{field}");
        for field in ["m", "k", "nTotal", "innerT"] {
            fun(&f(field), DomainSig::Unary(e(psd_k)), g(Ground::Nat));
        }
        for field in ["A", "N", "B", "Z"] {
            fun(
                &f(field),
                DomainSig::Unary(e(psd_k)),
                SortKey::TensorOf(Ground::Q),
            );
        }
        fun(
            &f("term"),
            record(&[("i", g(Ground::Nat)), ("p", e(psd_k))]),
            e(term),
        );
        fun(&f("conclusion"), DomainSig::Unary(e(psd_k)), e(term));
    }

    // The mask family's resolution chain + membership relations.
    {
        let simpc = ix.insert_sort("SimpC", next());
        let mut plain = |name: &str, domain: DomainSig, codomain: SortKey| {
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (PETRI_V0_REV, next()),
                relational: false,
                side_condition: false,
                domain,
                codomain: Some(codomain),
            });
        };
        plain(
            "SimpC/n_vertices",
            DomainSig::Unary(e(simpc)),
            g(Ground::Nat),
        );
        plain("Simplex/complex", DomainSig::Unary(e(simplex)), e(simpc));
        plain(
            "ExtensionSet/simplex",
            DomainSig::Unary(e(ext_set)),
            e(simplex),
        );
        let mut rel = |name: &str, domain: DomainSig| {
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (PETRI_V0_REV, next()),
                relational: true,
                side_condition: false,
                domain,
                codomain: None,
            });
        };
        rel(
            "Simplex/contains",
            record(&[("s", e(simplex)), ("v", g(Ground::Nat))]),
        );
        rel(
            "ExtensionSet/contains",
            record(&[("S", e(ext_set)), ("v", g(Ground::Nat))]),
        );
    }

    // The net-primary-data family (this vocabulary's own content).
    // Record fields in bytewise order — the wire argument order.
    {
        let pnet = ix.insert_sort("PNet", next());
        let pinv = ix.insert_sort("PInv", next());
        let mut fun = |name: &str, domain: DomainSig, codomain: SortKey| {
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (PETRI_V0_REV, next()),
                relational: false,
                side_condition: false,
                domain,
                codomain: Some(codomain),
            });
        };
        fun("PNet/places", DomainSig::Unary(e(pnet)), g(Ground::Nat));
        fun(
            "PNet/transitions",
            DomainSig::Unary(e(pnet)),
            g(Ground::Nat),
        );
        fun("PNet/invariants", DomainSig::Unary(e(pnet)), g(Ground::Nat));
        fun(
            "PNet/pre",
            record(&[
                ("net", e(pnet)),
                ("p", g(Ground::Nat)),
                ("t", g(Ground::Nat)),
            ]),
            g(Ground::Q),
        );
        fun(
            "PNet/post",
            record(&[
                ("net", e(pnet)),
                ("p", g(Ground::Nat)),
                ("t", g(Ground::Nat)),
            ]),
            g(Ground::Q),
        );
        fun(
            "PNet/m0",
            record(&[("net", e(pnet)), ("p", g(Ground::Nat))]),
            g(Ground::Q),
        );
        fun("PInv/net", DomainSig::Unary(e(pinv)), e(pnet));
        fun("PInv/index", DomainSig::Unary(e(pinv)), g(Ground::Nat));
        fun(
            "PInv/coeff",
            record(&[("inv", e(pinv)), ("p", g(Ground::Nat))]),
            g(Ground::Q),
        );
        fun("PInv/charge", DomainSig::Unary(e(pinv)), g(Ground::Q));
    }
    ix
}

/// The single obligation-relation name of the Petri lane's verdict
/// roster (every enumerated obligation — conservation identities and
/// initial charges — discharges through it).
pub const PETRI_V0_CLAIMS: [&str; 1] = ["constExactEvalTrue"];

/// Revision identifier of the v0 gym reward-table reproduction
/// vocabulary (same self-documenting-ASCII convention as
/// [`SPDE_V0_REV`]).
pub const GYMRW_V0_REV: [u8; 32] = *b"maitria-gymrw-vocab-v0\0\0\0\0\0\0\0\0\0\0";

/// The v0 gym reward-table reproduction vocabulary: finite-horizon
/// expected-total-reward certificates for tabular MDPs (the
/// certified-Gymnasium toy-text tier's reward-weighted lanes), as
/// sealed containers of PRIMARY DATA ONLY.
///
/// A certificate carries one `GymRwCert` element with its dimensions
/// (`ns` states, `na` actions, `deadline` T), an initial distribution
/// (weight rows over a common denominator `initDen`), an outcome-row
/// kernel (per (state, action, destination, reward) the numerator over
/// a per-group denominator — the reward is part of the row KEY, so the
/// same destination lawfully appears at two rewards), a time-varying
/// policy, a value table of numerator rows `w` over per-time
/// denominators `qden` (fixed-point certificates embed with every
/// `qden` = 2^k), and the claimed bound in Q:
///
/// ```text
/// E_pi[ sum_{t<T} r(X_t, A_t, X_{t+1}) | X_0 ~ init ] >= claim
/// ```
///
/// No derived quantities and no claim rows are stored: the checker
/// constructs the well-formedness / boundary / step / claim-mixture
/// obligations itself from the dimensions and discharges them through
/// the provider's `gymRwTableValid` walk ([`crate::gymrw`]) — the
/// recompute-from-primary discipline made total, as in the Petri
/// vocabulary. Single-letter record fields (bytewise order = wire
/// argument order): `c` certificate, `i` flat cell index, `s` state,
/// `t` time, `u` action, `x` destination state, `y` reward.
///
/// Policy and table rows are keyed by ONE flat cell index
/// `i = t·ns + s` (t-major, state-minor — the deadline-table species'
/// flat-list convention) rather than by (state, time) pairs: the
/// canonical body encoding columns every Nat literal cell, and its
/// pinned reader caps that column's row count, so per-cell key width
/// is a real capacity budget at the catalogue's largest tables
/// (belief-MDP taxi: 201k table cells; two Nat keys per cell would
/// exceed the cap that one flat key clears with a third of headroom).
///
/// Deterministic: every call constructs the identical index. Same
/// versioning law as [`fluid_v0`]: a change is a NEW vocabulary,
/// never an edit.
pub fn gymrw_v0() -> TheoryIndex {
    let mut ix = TheoryIndex::new(GYMRW_V0_REV);
    let mut ctr: u32 = 0;
    let mut next = || {
        ctr += 1;
        ctr
    };
    let cert = ix.insert_sort("GymRwCert", next());

    let e = SortKey::Elem;
    let g = SortKey::Ground;
    let mut fun = |name: &str, domain: DomainSig, codomain: SortKey| {
        ix.insert_fun(FunDecl {
            name: name.to_string(),
            chid: (GYMRW_V0_REV, next()),
            relational: false,
            side_condition: false,
            domain,
            codomain: Some(codomain),
        });
    };

    // Dimensions + claim (unary on the certificate element).
    fun("GymRwCert/ns", DomainSig::Unary(e(cert)), g(Ground::Nat));
    fun("GymRwCert/na", DomainSig::Unary(e(cert)), g(Ground::Nat));
    fun(
        "GymRwCert/deadline",
        DomainSig::Unary(e(cert)),
        g(Ground::Nat),
    );
    fun(
        "GymRwCert/initDen",
        DomainSig::Unary(e(cert)),
        g(Ground::Nat),
    );
    fun("GymRwCert/claim", DomainSig::Unary(e(cert)), g(Ground::Q));

    // Initial-distribution weight rows: (c, s) -> weight over initDen.
    fun(
        "GymRwCert/initW",
        record(&[("c", e(cert)), ("s", g(Ground::Nat))]),
        g(Ground::Nat),
    );
    // Per-group kernel denominator: (c, s, u) -> D.
    fun(
        "GymRwCert/kden",
        record(&[("c", e(cert)), ("s", g(Ground::Nat)), ("u", g(Ground::Nat))]),
        g(Ground::Nat),
    );
    // Outcome rows: (c, s, u, x, y) -> numerator n over the group's D.
    fun(
        "GymRwCert/kout",
        record(&[
            ("c", e(cert)),
            ("s", g(Ground::Nat)),
            ("u", g(Ground::Nat)),
            ("x", g(Ground::Nat)),
            ("y", g(Ground::Q)),
        ]),
        g(Ground::Nat),
    );
    // Policy rows: (c, i = t*ns + s) -> action, for t < T.
    fun(
        "GymRwCert/pact",
        record(&[("c", e(cert)), ("i", g(Ground::Nat))]),
        g(Ground::Nat),
    );
    // Per-time table denominators: (c, t) -> Q_t (positive integer).
    fun(
        "GymRwCert/qden",
        record(&[("c", e(cert)), ("t", g(Ground::Nat))]),
        g(Ground::Q),
    );
    // Table numerator rows: (c, i = t*ns + s) -> w_t(s) (signed
    // integer), for t <= T.
    fun(
        "GymRwCert/w",
        record(&[("c", e(cert)), ("i", g(Ground::Nat))]),
        g(Ground::Q),
    );

    // The walk relation (the side condition the checker demands on
    // every GymRwCert element).
    ix.insert_fun(FunDecl {
        name: "gymRwTableValid".to_string(),
        chid: (GYMRW_V0_REV, next()),
        relational: true,
        side_condition: true,
        domain: DomainSig::Unary(e(cert)),
        codomain: None,
    });
    ix
}

/// The single claim-relation name of [`gymrw_v0`]'s verdict roster.
pub const GYMRW_V0_CLAIMS: [&str; 1] = ["gymRwTableValid"];
/// Revision identifier of the v0 gymnasium e-process reproduction
/// vocabulary (same self-documenting-ASCII convention as
/// [`SPDE_V0_REV`]).
pub const GYMEPROC_V0_REV: [u8; 32] = *b"maitria-gymeproc-vocab-v0\0\0\0\0\0\0\0";

/// The v0 gymnasium e-process reproduction vocabulary: anytime-valid
/// lower confidence bounds on the expected episodic return of a fixed
/// policy, certified from an i.i.d. rollout ledger by a
/// betting-martingale mixture with a randomized last look.
///
/// A certificate carries PRIMARY DATA ONLY — the protocol constants
/// (`alphaInv`, the scale pair `kLo < kHi`, the claim class, the
/// claimed boundary `m*` as the schema's 96-bit `[hi, lo]` pair used
/// exactly, the declared episode count), the rollout ledger verbatim
/// (episode returns as exact rationals, chunked into inline rank-1
/// `TensorOf(Q)` rows), the claimed bounds in raw units, and — when
/// the randomized-last-look claim is made — the drawn `u` with its
/// declared protocol provenance. The checker recomputes the entire
/// mixture-wealth walk in Q32.96 fixed point (every rounding directed
/// down) from these rows at every discharge; wealth values, scaled
/// observables, and the bet grid are never stored (the grid is
/// checker-hardcoded, so a grid tamper is unrepresentable rather than
/// discouraged).
///
/// Two claim classes, never mixed silently — the class is an explicit
/// constructor row, so its absence refuses rather than defaulting:
///
/// - `qecMinCap`: the observable is `min(R, kHi)`; soundness consumes
///   the producer's range lemma `R >= kLo` a.s., and every ledger
///   entry is checked against it (a violating entry refuses the
///   certificate, carrying the entry as the lemma's refutation
///   witness).
/// - `qecClip(lo)`: the truncated-mean claim `E[clip(R, lo, kHi)]`;
///   requires `lo == kLo` (tight scale), consumes no range lemma.
///
/// The drawn `u` is a protocol record: its drawn-after-and-independent
/// provenance rides a declared `Str` row verbatim and is not
/// machine-checkable — which is why the deterministic verdict is a
/// separate claim relation discharged alongside.
///
/// Deterministic: every call constructs the identical index. Same
/// versioning law as [`fluid_v0`]: a change is a NEW vocabulary,
/// never an edit.
pub fn gymeproc_v0() -> TheoryIndex {
    let mut ix = TheoryIndex::new(GYMEPROC_V0_REV);
    let mut ctr: u32 = 0;
    let mut next = || {
        ctr += 1;
        ctr
    };
    let cert = ix.insert_sort("QEprocCert", next());
    let class = ix.insert_sort("QEprocClass", next());
    let look = ix.insert_sort("QEprocLook", next());

    let e = SortKey::Elem;
    let g = SortKey::Ground;
    let mut fun = |name: &str, domain: DomainSig, codomain: SortKey| {
        ix.insert_fun(FunDecl {
            name: name.to_string(),
            chid: (GYMEPROC_V0_REV, next()),
            relational: false,
            side_condition: false,
            domain,
            codomain: Some(codomain),
        });
    };

    // The claim class (explicit constructor — absence refuses).
    fun("qecMinCap", DomainSig::Nullary, e(class));
    fun("qecClip", DomainSig::Unary(g(Ground::Z)), e(class));

    // Protocol constants.
    fun(
        "QEprocCert/alphaInv",
        DomainSig::Unary(e(cert)),
        g(Ground::Nat),
    );
    fun("QEprocCert/kLo", DomainSig::Unary(e(cert)), g(Ground::Z));
    fun("QEprocCert/kHi", DomainSig::Unary(e(cert)), g(Ground::Z));
    fun("QEprocCert/class", DomainSig::Unary(e(cert)), e(class));
    fun(
        "QEprocCert/mDetHi",
        DomainSig::Unary(e(cert)),
        g(Ground::Nat),
    );
    fun(
        "QEprocCert/mDetLo",
        DomainSig::Unary(e(cert)),
        g(Ground::Nat),
    );
    fun(
        "QEprocCert/episodes",
        DomainSig::Unary(e(cert)),
        g(Ground::Nat),
    );
    // The claimed deterministic bound in raw units, exact rational
    // (tie-checked against kLo + mDet·(kHi−kLo)/2^96 at discharge).
    fun(
        "QEprocCert/boundDet",
        DomainSig::Unary(e(cert)),
        g(Ground::Q),
    );

    // The rollout ledger, verbatim: chunked rank-1 inline tensors of
    // exact-rational episode returns, chunk indices dense from 0.
    fun(
        "QEprocCert/retChunk",
        record(&[("c", e(cert)), ("i", g(Ground::Nat))]),
        SortKey::TensorOf(Ground::Q),
    );

    // The randomized last look (presence = the claim is made).
    fun("QEprocCert/look", DomainSig::Unary(e(cert)), e(look));
    fun(
        "QEprocLook/mRandHi",
        DomainSig::Unary(e(look)),
        g(Ground::Nat),
    );
    fun(
        "QEprocLook/mRandLo",
        DomainSig::Unary(e(look)),
        g(Ground::Nat),
    );
    fun("QEprocLook/u", DomainSig::Unary(e(look)), g(Ground::Q));
    fun(
        "QEprocLook/uProtocol",
        DomainSig::Unary(e(look)),
        g(Ground::Str),
    );
    fun(
        "QEprocLook/boundRand",
        DomainSig::Unary(e(look)),
        g(Ground::Q),
    );

    // The two claim relations (side conditions the checker discharges
    // through the ground provider).
    {
        let mut side = |name: &str, domain: DomainSig| {
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (GYMEPROC_V0_REV, next()),
                relational: true,
                side_condition: true,
                domain,
                codomain: None,
            });
        };
        side("gymEprocDetValid", DomainSig::Unary(e(cert)));
        side("gymEprocRandValid", DomainSig::Unary(e(cert)));
    }
    ix
}

/// The two claim-relation names of [`gymeproc_v0`], in dispatch
/// report order.
pub const GYMEPROC_V0_CLAIMS: [&str; 2] = ["gymEprocDetValid", "gymEprocRandValid"];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic_and_resolvable() {
        let a = fluid_v0();
        let b = fluid_v0();
        assert_eq!(a.commit, FLUID_V0_REV);
        assert_eq!(a.funs.len(), b.funs.len());
        for (fa, fb) in a.funs.iter().zip(b.funs.iter()) {
            assert_eq!(fa.name, fb.name);
            assert_eq!(fa.chid, fb.chid);
        }
        for name in FLUID_V0_CLAIMS {
            let d = a.fun(name).expect("claim relation declared");
            assert!(d.relational && d.side_condition);
        }
        // The BL vocabulary must resolve over this index (the claim
        // declarations must not perturb resolution).
        let vocab = crate::QtslVocab::build(&[&a]);
        assert!(
            vocab.bl.is_some(),
            "BL vocabulary resolves: {:?}",
            vocab.notes
        );
    }

    #[test]
    fn spde_v0_deterministic_and_resolvable() {
        let a = spde_v0();
        let b = spde_v0();
        assert_eq!(a.commit, SPDE_V0_REV);
        assert_ne!(SPDE_V0_REV, FLUID_V0_REV, "vocabulary revisions distinct");
        assert_eq!(a.funs.len(), b.funs.len());
        for (fa, fb) in a.funs.iter().zip(b.funs.iter()) {
            assert_eq!(fa.name, fb.name);
            assert_eq!(fa.chid, fb.chid);
        }
        for name in SPDE_V0_CLAIMS {
            let d = a.fun(name).expect("claim relation declared");
            assert!(d.relational && d.side_condition);
        }
        // The spdemoment vocabulary must resolve over this index.
        let vocab = crate::QtslVocab::build(&[&a]);
        assert!(
            vocab.spdemoment.is_some(),
            "spdemoment vocabulary resolves: {:?}",
            vocab.notes
        );
    }

    #[test]
    fn joint_roster_resolves_both_families() {
        // The `.glc` checker builds ONE provider over every rostered
        // vocabulary; both families must resolve side by side.
        let f = fluid_v0();
        let s = spde_v0();
        let vocab = crate::QtslVocab::build(&[&f, &s]);
        assert!(
            vocab.bl.is_some(),
            "bl over joint roster: {:?}",
            vocab.notes
        );
        assert!(
            vocab.spdemoment.is_some(),
            "spdemoment over joint roster: {:?}",
            vocab.notes
        );
    }

    #[test]
    fn petri_v0_deterministic_and_resolvable() {
        let a = petri_v0();
        let b = petri_v0();
        assert_eq!(a.commit, PETRI_V0_REV);
        assert_ne!(PETRI_V0_REV, FLUID_V0_REV, "vocabulary revisions distinct");
        assert_ne!(PETRI_V0_REV, SPDE_V0_REV, "vocabulary revisions distinct");
        assert_eq!(a.funs.len(), b.funs.len());
        for (fa, fb) in a.funs.iter().zip(b.funs.iter()) {
            assert_eq!(fa.name, fb.name);
            assert_eq!(fa.chid, fb.chid);
        }
        // No claim relation is DECLARED (a Petri certificate has no
        // lawful claim row) — but the provider must still CLAIM
        // constExactEvalTrue once the BL group resolves.
        assert!(a.fun("constExactEvalTrue").is_none());
        assert!(a.fun("farkasCombinationValid").is_none());
        let vocab = crate::QtslVocab::build(&[&a]);
        assert!(
            vocab.bl.is_some(),
            "BL vocabulary resolves over petri_v0: {:?}",
            vocab.notes
        );
        let provider =
            crate::QtslGroundProvider::new(vec![[0x2F; 32]], crate::QtslVocab::build(&[&a]));
        assert!(
            provider.local_by_name("constExactEvalTrue").is_some(),
            "constExactEvalTrue claimed via the BL group"
        );
    }

    #[test]
    fn petri_v0_pinned_counters() {
        // The producer duplicates this index construction
        // (the landing-independence posture); these pins are the
        // cross-repo tie a drifted duplicate fails against.
        let a = petri_v0();
        let pin = |name: &str, ctr: u32| {
            assert_eq!(
                a.fun(name)
                    .unwrap_or_else(|| panic!("{name} declared"))
                    .chid,
                (PETRI_V0_REV, ctr),
                "counter pin for {name}"
            );
        };
        assert_eq!(a.sort("PNet").expect("PNet sort"), (PETRI_V0_REV, 79));
        assert_eq!(a.sort("PInv").expect("PInv sort"), (PETRI_V0_REV, 80));
        pin("PNet/places", 81);
        pin("PNet/transitions", 82);
        pin("PNet/invariants", 83);
        pin("PNet/pre", 84);
        pin("PNet/post", 85);
        pin("PNet/m0", 86);
        pin("PInv/net", 87);
        pin("PInv/index", 88);
        pin("PInv/coeff", 89);
        pin("PInv/charge", 90);
        pin("TConst", 17);
        pin("TAdd", 18);
        pin("TMul", 19);
        pin("TSub", 20);
        assert_eq!(a.sort("Term").expect("Term sort"), (PETRI_V0_REV, 1));
    }

    #[test]
    fn gymrw_v0_deterministic_and_resolvable() {
        let a = gymrw_v0();
        let b = gymrw_v0();
        assert_eq!(a.commit, GYMRW_V0_REV);
        assert_ne!(GYMRW_V0_REV, FLUID_V0_REV, "vocabulary revisions distinct");
        assert_ne!(GYMRW_V0_REV, SPDE_V0_REV, "vocabulary revisions distinct");
        assert_ne!(GYMRW_V0_REV, PETRI_V0_REV, "vocabulary revisions distinct");
        assert_eq!(a.funs.len(), b.funs.len());
        for (fa, fb) in a.funs.iter().zip(b.funs.iter()) {
            assert_eq!(fa.name, fb.name);
            assert_eq!(fa.chid, fb.chid);
        }
        for name in GYMRW_V0_CLAIMS {
            let d = a.fun(name).expect("claim relation declared");
            assert!(d.relational && d.side_condition);
        }
        // The family is standalone: no Term/Formula substrate needed —
        // its own vocabulary group must resolve, and the provider must
        // claim the walk relation over it.
        let vocab = crate::QtslVocab::build(&[&a]);
        assert!(
            vocab.gymrw.is_some(),
            "gymrw vocabulary resolves: {:?}",
            vocab.notes
        );
        let provider =
            crate::QtslGroundProvider::new(vec![[0x2F; 32]], crate::QtslVocab::build(&[&a]));
        assert!(
            provider.local_by_name("gymRwTableValid").is_some(),
            "gymRwTableValid claimed via the gymrw group"
        );
    }

    #[test]
    fn gymrw_v0_pinned_counters() {
        // The mtk-side producer duplicates this index construction as
        // pinned constants (landing-independence posture); these pins
        // are the cross-repo tie a drifted duplicate fails against.
        let a = gymrw_v0();
        let pin = |name: &str, ctr: u32| {
            assert_eq!(
                a.fun(name)
                    .unwrap_or_else(|| panic!("{name} declared"))
                    .chid,
                (GYMRW_V0_REV, ctr),
                "counter pin for {name}"
            );
        };
        assert_eq!(
            a.sort("GymRwCert").expect("GymRwCert sort"),
            (GYMRW_V0_REV, 1)
        );
        pin("GymRwCert/ns", 2);
        pin("GymRwCert/na", 3);
        pin("GymRwCert/deadline", 4);
        pin("GymRwCert/initDen", 5);
        pin("GymRwCert/claim", 6);
        pin("GymRwCert/initW", 7);
        pin("GymRwCert/kden", 8);
        pin("GymRwCert/kout", 9);
        pin("GymRwCert/pact", 10);
        pin("GymRwCert/qden", 11);
        pin("GymRwCert/w", 12);
        pin("gymRwTableValid", 13);
    }

    #[test]
    fn petri_v0_needs_its_own_provider() {
        // petri_v0 deliberately re-declares the BL shape names (Term,
        // Simplex, …) under its own revision — required for the BL
        // group to resolve — so a JOINT sweep with fluid_v0 is
        // ambiguous by construction. The checker's architecture is
        // one provider PER mode (as for fluid/bl/spde already); this
        // test pins that a joint build refuses rather than guessing.
        let f = fluid_v0();
        let p = petri_v0();
        let vocab = crate::QtslVocab::build(&[&f, &p]);
        assert!(
            vocab.bl.is_none(),
            "joint fluid+petri sweep must refuse the ambiguous names"
        );
    }

    #[test]
    fn gymeproc_v0_deterministic_and_resolvable() {
        let a = gymeproc_v0();
        let b = gymeproc_v0();
        assert_eq!(a.commit, GYMEPROC_V0_REV);
        for other in [FLUID_V0_REV, SPDE_V0_REV, PETRI_V0_REV] {
            assert_ne!(GYMEPROC_V0_REV, other, "vocabulary revisions distinct");
        }
        assert_eq!(a.funs.len(), b.funs.len());
        for (fa, fb) in a.funs.iter().zip(b.funs.iter()) {
            assert_eq!(fa.name, fb.name);
            assert_eq!(fa.chid, fb.chid);
        }
        for name in GYMEPROC_V0_CLAIMS {
            let d = a.fun(name).expect("claim relation declared");
            assert!(d.relational && d.side_condition);
        }
        let vocab = crate::QtslVocab::build(&[&a]);
        assert!(
            vocab.gymeproc.is_some(),
            "gymeproc vocabulary resolves: {:?}",
            vocab.notes
        );
    }

    #[test]
    fn gymeproc_v0_pinned_counters() {
        // The mtk producer duplicates this index construction (the
        // landing-independence posture); these pins are the cross-repo
        // tie a drifted duplicate fails against.
        let a = gymeproc_v0();
        let pin = |name: &str, ctr: u32| {
            assert_eq!(
                a.fun(name)
                    .unwrap_or_else(|| panic!("{name} declared"))
                    .chid,
                (GYMEPROC_V0_REV, ctr),
                "counter pin for {name}"
            );
        };
        assert_eq!(a.sort("QEprocCert").expect("sort"), (GYMEPROC_V0_REV, 1));
        assert_eq!(a.sort("QEprocClass").expect("sort"), (GYMEPROC_V0_REV, 2));
        assert_eq!(a.sort("QEprocLook").expect("sort"), (GYMEPROC_V0_REV, 3));
        pin("qecMinCap", 4);
        pin("qecClip", 5);
        pin("QEprocCert/alphaInv", 6);
        pin("QEprocCert/kLo", 7);
        pin("QEprocCert/kHi", 8);
        pin("QEprocCert/class", 9);
        pin("QEprocCert/mDetHi", 10);
        pin("QEprocCert/mDetLo", 11);
        pin("QEprocCert/episodes", 12);
        pin("QEprocCert/boundDet", 13);
        pin("QEprocCert/retChunk", 14);
        pin("QEprocCert/look", 15);
        pin("QEprocLook/mRandHi", 16);
        pin("QEprocLook/mRandLo", 17);
        pin("QEprocLook/u", 18);
        pin("QEprocLook/uProtocol", 19);
        pin("QEprocLook/boundRand", 20);
        pin("gymEprocDetValid", 21);
        pin("gymEprocRandValid", 22);
    }
}
