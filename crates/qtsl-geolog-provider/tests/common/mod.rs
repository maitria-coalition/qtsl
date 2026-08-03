#![allow(dead_code)]

//! Shared test fixture: a synthetic declaration index carrying the
//! QTSL certificate vocabulary with the same declared shapes as the
//! theory source (sorts, constructor signatures, field signatures —
//! record fields in bytewise order, which fixes wire argument order),
//! plus the provider built over it and a verdict-shaped eval helper.
//!
//! The synthetic index stands in for the engine's theory loaders: the
//! provider's vocabulary resolution consumes declaration DATA, so a
//! test can mint pinned identities directly — what matters (and what
//! these fixtures preserve exactly) is the declared shape of every
//! entry, because the resolvers verify shapes and the structural walks
//! consult per-position sorts.

use geolog_ground_api::Verdict;
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::{Chid, DomainSig, FunDecl, Ground, SortKey, TheoryIndex};
use qtsl_geolog_provider::{QtslGroundProvider, QtslVocab};
use std::sync::OnceLock;

/// The synthetic stack revision's commit hash.
pub const STACK: [u8; 32] = [0x51; 32];

/// The semantics revision the test provider claims coverage of.
pub const REV: [u8; 32] = [0x5E; 32];

fn record(fields: &[(&str, SortKey)]) -> DomainSig {
    DomainSig::Record(fields.iter().map(|(n, s)| (n.to_string(), *s)).collect())
}

/// The declaration index, shapes transcribed from the theory source:
///
/// ```text
/// TVar : Wire -> Term                 TConst : Q -> Term
/// TAdd/TMul/TSub : [l,r: Term] -> Term    TNeg : Term -> Term
/// TIdx : [t: Term, i: Nat] -> Term    THole : () -> Term
/// FAtom{LT,LE,EQ,GE,GT,NE} : [l,r: Term] -> Formula
/// FAnd/FOr : [l,r: Formula] -> Formula
/// FTrue/FFalse/FSpH : () -> Formula
/// FInRegion : [t: Term, simplex: Simplex, S: ExtensionSet] -> Formula
/// Judgment/pre, Judgment/post : Judgement -> Formula
/// Proof/concludes : Proof -> Judgement
/// Wire/type : Wire -> TensorType
/// mkTensorType : [shape: Shape, dtype: Dtype] -> TensorType
/// empty : () -> Shape      cons : [head: Nat, tail: Shape] -> Shape
/// P<node>/… per the combination-node and PSD-certificate families
/// ```
///
/// (Record fields appear below in bytewise order — the wire argument
/// order — e.g. TIdx as `[i, t]`, mkTensorType as `[dtype, shape]`.)
pub fn stack() -> &'static TheoryIndex {
    static IX: OnceLock<TheoryIndex> = OnceLock::new();
    IX.get_or_init(|| {
        let mut ix = TheoryIndex::new(STACK);
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
        // The Dtype theory's axis sorts (the float lane's vocabulary;
        // appended after the original block so earlier chids are
        // unshifted).
        let kind_sort = ix.insert_sort("Kind", next());
        let sign_sort = ix.insert_sort("Sign", next());
        let ext_axis = ix.insert_sort("Ext", next());

        let e = SortKey::Elem;
        let g = SortKey::Ground;
        let mut fun = |name: &str, domain: DomainSig, codomain: SortKey| {
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (STACK, next()),
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

        // The Dtype theory (the float lane's vocabulary): axis fields,
        // the constructor, and the nullary constants — shaped as the
        // normalized stack declares them.
        fun("Dtype/kind", DomainSig::Unary(e(dtype)), e(kind_sort));
        fun("Dtype/sign", DomainSig::Unary(e(dtype)), e(sign_sort));
        fun("Dtype/ext", DomainSig::Unary(e(dtype)), e(ext_axis));
        fun(
            "mkDtype",
            record(&[("k", e(kind_sort)), ("s", e(sign_sort)), ("e", e(ext_axis))]),
            e(dtype),
        );
        for k in ["KBool", "KInt", "KRat", "KF16", "KF16bf", "KF32", "KF64"] {
            fun(k, DomainSig::Nullary, e(kind_sort));
        }
        for s in ["Snn", "Ss"] {
            fun(s, DomainSig::Nullary, e(sign_sort));
        }
        for x in ["Efin", "Eext"] {
            fun(x, DomainSig::Nullary, e(ext_axis));
        }
        for a in ["Q", "Z", "Nat", "B", "F64"] {
            fun(a, DomainSig::Nullary, e(dtype));
        }

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

        // PSD certificate nodes: the square witnesses (T and DD)…
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
        // …and the kernel-completion node.
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

        // The mask family's vocabulary: the resolution chain
        // (ExtensionSet/simplex → Simplex/complex → SimpC/n_vertices)
        // plus the two membership relations — RELATIONAL declarations
        // (no codomain), exactly as the theory source shapes them.
        {
            let simpc = ix.insert_sort("SimpC", next());
            let mut plain = |name: &str, domain: DomainSig, codomain: SortKey| {
                ix.insert_fun(FunDecl {
                    name: name.to_string(),
                    chid: (STACK, next()),
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
            plain("SimpC/amb_dim", DomainSig::Unary(e(simpc)), g(Ground::Nat));
            // Field order bytewise: complex < j < v.
            plain(
                "SimpC/coord",
                record(&[
                    ("complex", e(simpc)),
                    ("j", g(Ground::Nat)),
                    ("v", g(Ground::Nat)),
                ]),
                g(Ground::Q),
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
                    chid: (STACK, next()),
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

            // The cell-application vocabulary (the cell-schema
            // conclusion forms): hypernet port fields, shapes
            // transcribed from the theory source, plus the certificate
            // extension's cell-list rows (`SimpC/nCells` and the two
            // cell-mask relations, shapes transcribed from the
            // certificate-extension theory).
            let primapp = ix.insert_sort("PrimApp", next());
            let input_port = ix.insert_sort("InputPort", next());
            let output_port = ix.insert_sort("OutputPort", next());
            let mut plain2 = |name: &str, domain: DomainSig, codomain: SortKey| {
                ix.insert_fun(FunDecl {
                    name: name.to_string(),
                    chid: (STACK, next()),
                    relational: false,
                    side_condition: false,
                    domain,
                    codomain: Some(codomain),
                });
            };
            plain2("InputPort/app", DomainSig::Unary(e(input_port)), e(primapp));
            plain2(
                "InputPort/pos",
                DomainSig::Unary(e(input_port)),
                g(Ground::Nat),
            );
            plain2("InputPort/wire", DomainSig::Unary(e(input_port)), e(wire));
            plain2(
                "OutputPort/app",
                DomainSig::Unary(e(output_port)),
                e(primapp),
            );
            plain2(
                "OutputPort/pos",
                DomainSig::Unary(e(output_port)),
                g(Ground::Nat),
            );
            plain2("OutputPort/wire", DomainSig::Unary(e(output_port)), e(wire));
            plain2("SimpC/nCells", DomainSig::Unary(e(simpc)), g(Ground::Nat));
            let mut rel2 = |name: &str, domain: DomainSig| {
                ix.insert_fun(FunDecl {
                    name: name.to_string(),
                    chid: (STACK, next()),
                    relational: true,
                    side_condition: false,
                    domain,
                    codomain: None,
                });
            };
            // Wire field order (bytewise): cell, complex, v.
            rel2(
                "CellSimplexHasV",
                record(&[
                    ("cell", g(Ground::Nat)),
                    ("complex", e(simpc)),
                    ("v", g(Ground::Nat)),
                ]),
            );
            rel2(
                "CellExtHasV",
                record(&[
                    ("cell", g(Ground::Nat)),
                    ("complex", e(simpc)),
                    ("v", g(Ground::Nat)),
                ]),
            );
        }

        // The block-lattice family's vocabulary: the lattice / axis /
        // block / judgment / product-node fields. Its interval atoms
        // read the same simplicial chain declared above (including
        // `SimpC/amb_dim` and `SimpC/coord`, shared with the
        // barycentric vocabulary — declared ONCE: a duplicate would
        // make name resolution ambiguous and unclaim both families).
        // Record fields in bytewise order, as everywhere in this
        // fixture.
        {
            let bl = ix.insert_sort("BlockLattice", next());
            let axis = ix.insert_sort("BLAxis", next());
            let fblock = ix.insert_sort("FamBlock", next());
            let famj = ix.insert_sort("FamJudgment", next());
            let prod = ix.insert_sort("PProductLattice", next());
            let mut plain = |name: &str, domain: DomainSig, codomain: SortKey| {
                ix.insert_fun(FunDecl {
                    name: name.to_string(),
                    chid: (STACK, next()),
                    relational: false,
                    side_condition: false,
                    domain,
                    codomain: Some(codomain),
                });
            };
            plain(
                "BlockLattice/nAxes",
                DomainSig::Unary(e(bl)),
                g(Ground::Nat),
            );
            plain(
                "BlockLattice/nBlocks",
                DomainSig::Unary(e(bl)),
                g(Ground::Nat),
            );
            plain("BLAxis/lattice", DomainSig::Unary(e(axis)), e(bl));
            plain("BLAxis/index", DomainSig::Unary(e(axis)), g(Ground::Nat));
            plain("BLAxis/wire", DomainSig::Unary(e(axis)), e(wire));
            plain("BLAxis/drift", DomainSig::Unary(e(axis)), e(term));
            plain(
                "BLAxis/nGridlines",
                DomainSig::Unary(e(axis)),
                g(Ground::Nat),
            );
            plain(
                "BLAxis/gridline",
                record(&[("g", g(Ground::Nat)), ("x", e(axis))]),
                g(Ground::Q),
            );
            plain("FamBlock/lattice", DomainSig::Unary(e(fblock)), e(bl));
            plain(
                "FamBlock/index",
                DomainSig::Unary(e(fblock)),
                g(Ground::Nat),
            );
            plain(
                "FamBlock/nCells",
                DomainSig::Unary(e(fblock)),
                g(Ground::Nat),
            );
            plain(
                "FamBlock/cell",
                record(&[("b", e(fblock)), ("c", g(Ground::Nat))]),
                g(Ground::Nat),
            );
            plain(
                "FamBlock/nFacets",
                DomainSig::Unary(e(fblock)),
                g(Ground::Nat),
            );
            plain(
                "FamBlock/facetProof",
                record(&[("b", e(fblock)), ("f", g(Ground::Nat))]),
                e(proof),
            );
            plain("FamJudgment/lattice", DomainSig::Unary(e(famj)), e(bl));
            plain(
                "PProductLattice/concludes",
                DomainSig::Unary(e(prod)),
                e(famj),
            );
            plain("PProductLattice/left", DomainSig::Unary(e(prod)), e(bl));
            plain("PProductLattice/right", DomainSig::Unary(e(prod)), e(bl));
            plain(
                "PProductLattice/flowsOnly",
                DomainSig::Unary(e(prod)),
                g(Ground::Nat),
            );
        }

        // The surgery family's path vocabulary (CtxPath constructors,
        // shapes transcribed from the theory source):
        // PathHere : () -> CtxPath, PathL/PathR : CtxPath -> CtxPath.
        {
            let ctxpath = ix.insert_sort("CtxPath", next());
            let mut plain = |name: &str, domain: DomainSig| {
                ix.insert_fun(FunDecl {
                    name: name.to_string(),
                    chid: (STACK, next()),
                    relational: false,
                    side_condition: false,
                    domain,
                    codomain: Some(e(ctxpath)),
                });
            };
            plain("PathHere", DomainSig::Nullary);
            plain("PathL", DomainSig::Unary(e(ctxpath)));
            plain("PathR", DomainSig::Unary(e(ctxpath)));
        }

        // The enclosure family's vocabulary: the remainder-bound
        // judgment's four fields (func/n Nat, r/cap Q), shapes
        // transcribed from the theory source. The EncJudgment sort is
        // declared HERE ONLY (a duplicate declaration elsewhere in
        // this fixture would make name resolution ambiguous and
        // unclaim the family).
        {
            let encj = ix.insert_sort("EncJudgment", next());
            let mut plain = |name: &str, codomain: SortKey| {
                ix.insert_fun(FunDecl {
                    name: name.to_string(),
                    chid: (STACK, next()),
                    relational: false,
                    side_condition: false,
                    domain: DomainSig::Unary(e(encj)),
                    codomain: Some(codomain),
                });
            };
            plain("EncJudgment/func", g(Ground::Nat));
            plain("EncJudgment/n", g(Ground::Nat));
            plain("EncJudgment/r", g(Ground::Q));
            plain("EncJudgment/cap", g(Ground::Q));
        }

        // The promise family's vocabulary: the
        // PPromise node fields, shapes transcribed from the theory
        // source (proof/supplier/consumer are Proof-valued, contract
        // Formula, path CtxPath, nIfaceWires Nat, and the indexed
        // iface family in bytewise field order `k` < `p` — appended
        // here so every existing chid is unchanged).
        {
            let ppromise = ix.insert_sort("PPromise", next());
            let ctxpath = ix.sort("CtxPath").expect("declared above");
            let mut plain = |name: &str, domain: DomainSig, codomain: SortKey| {
                ix.insert_fun(FunDecl {
                    name: name.to_string(),
                    chid: (STACK, next()),
                    relational: false,
                    side_condition: false,
                    domain,
                    codomain: Some(codomain),
                });
            };
            plain("PPromise/proof", DomainSig::Unary(e(ppromise)), e(proof));
            plain("PPromise/supplier", DomainSig::Unary(e(ppromise)), e(proof));
            plain("PPromise/consumer", DomainSig::Unary(e(ppromise)), e(proof));
            plain(
                "PPromise/contract",
                DomainSig::Unary(e(ppromise)),
                e(formula),
            );
            plain("PPromise/path", DomainSig::Unary(e(ppromise)), e(ctxpath));
            plain(
                "PPromise/nIfaceWires",
                DomainSig::Unary(e(ppromise)),
                g(Ground::Nat),
            );
            plain(
                "PPromise/ifaceWire",
                record(&[("k", g(Ground::Nat)), ("p", e(ppromise))]),
                e(wire),
            );
        }

        // The Bernstein-cone family's subdivision vocabulary (G2
        // leg 4): the PSubdivide node's branch-count field and the two
        // indexed branch families, shapes transcribed from the theory
        // source (indexed families in bytewise field order `k` < `p` —
        // appended here so every existing chid is unchanged). The
        // coefficient sweep itself needs no new vocabulary: its five
        // fields are the Simplex/ExtensionSet/Term/Formula sorts
        // declared above.
        {
            let psub = ix.insert_sort("PSubdivide", next());
            let mut plain = |name: &str, domain: DomainSig, codomain: SortKey| {
                ix.insert_fun(FunDecl {
                    name: name.to_string(),
                    chid: (STACK, next()),
                    relational: false,
                    side_condition: false,
                    domain,
                    codomain: Some(codomain),
                });
            };
            plain(
                "PSubdivide/nBranches",
                DomainSig::Unary(e(psub)),
                g(Ground::Nat),
            );
            plain(
                "PSubdivide/branchSimplex",
                record(&[("k", g(Ground::Nat)), ("p", e(psub))]),
                e(simplex),
            );
            plain(
                "PSubdivide/branchS",
                record(&[("k", g(Ground::Nat)), ("p", e(psub))]),
                e(ext_set),
            );
        }

        {
            // The NN conclusion-form + semiring-cell
            // vocabularies: the primitive tag, the `PReLU`/`PContract`
            // constructors, and the HAggKind cell relation — shapes
            // transcribed from the theory source. Appended at the END
            // of the builder so every pre-existing synthetic chid is
            // unchanged.
            let e = SortKey::Elem;
            let g = SortKey::Ground;
            let primapp = ix.sort("PrimApp").expect("PrimApp declared above");
            let primitive = ix.insert_sort("Primitive", next());
            let haggkind = ix.insert_sort("HAggKind", next());
            let mut plain = |name: &str, domain: DomainSig, codomain: SortKey| {
                ix.insert_fun(FunDecl {
                    name: name.to_string(),
                    chid: (STACK, next()),
                    relational: false,
                    side_condition: false,
                    domain,
                    codomain: Some(codomain),
                });
            };
            plain("PrimApp/prim", DomainSig::Unary(e(primapp)), e(primitive));
            plain("PReLU", DomainSig::Nullary, e(primitive));
            plain("PContract", DomainSig::Nullary, e(primitive));
            for k in ["hagSum", "hagMax", "hagMin", "hagConjPow", "hagConjExp"] {
                plain(k, DomainSig::Nullary, e(haggkind));
            }
            ix.insert_fun(FunDecl {
                name: "contract_semiring".to_string(),
                chid: (STACK, next()),
                relational: true,
                side_condition: false,
                domain: record(&[
                    ("app", e(primapp)),
                    ("kind", e(haggkind)),
                    ("param", g(Ground::Q)),
                ]),
                codomain: None,
            });
        }
        ix
    })
}

/// The synthetic certificate-extension revision's commit hash.
pub const QTSLCERT: [u8; 32] = [0x9C; 32];

/// The certificate-extension index: the Bag canonical-multiset value
/// vocabulary, shapes transcribed from the theory source:
///
/// ```text
/// qbagMk : [dim: Nat, tokens: QBagTokList] -> QBagVal
/// qbtNil : () -> QBagTokList
/// qbtCons : [head: QRatList, tail: QBagTokList] -> QBagTokList
/// qrlNil : () -> QRatList
/// qrlCons : [head: Q, tail: QRatList] -> QRatList
/// ```
///
/// (The other recompute families' vocabularies — Morse readout,
/// Miranda battery, stochastic-wire — are deliberately absent: the
/// provider must NOT claim them here, and the seam battery pins that.)
pub fn qtslcert() -> &'static TheoryIndex {
    static IX: OnceLock<TheoryIndex> = OnceLock::new();
    IX.get_or_init(|| {
        let mut ix = TheoryIndex::new(QTSLCERT);
        let bag = ix.insert_sort("QBagVal", 1);
        let toklist = ix.insert_sort("QBagTokList", 2);
        let ratlist = ix.insert_sort("QRatList", 3);
        let plog_prog = ix.insert_sort("QPlogProg", 4);
        let plog_coins = ix.insert_sort("QPlogCoinList", 5);
        let plog_facts = ix.insert_sort("QPlogFactList", 6);
        let plog_clauses = ix.insert_sort("QPlogClauseList", 7);
        let plog_sets = ix.insert_sort("QPlogSetList", 8);
        // The compiled decision-term sorts (ids 60+
        // keep every existing sort id unchanged).
        let plog_dectree = ix.insert_sort("QPlogDecTree", 60);
        let plog_armlist = ix.insert_sort("QPlogArmList", 61);
        // The carillon family's sorts (counters 40+
        // keep the existing chids unchanged). Box/Interval live in
        // the Qtsl-theory index (cross-revision references, as in
        // the theory source).
        let boxs = qtslsys().sort("Box").expect("qtslsys Box sort");
        let gridcx = ix.insert_sort("QGridCx", 40);
        let patchtree = ix.insert_sort("QPatchTree", 41);
        let chartref = ix.insert_sort("QChartRef", 42);
        let genlist = ix.insert_sort("QGenList", 43);
        let groupgen = ix.insert_sort("QGroupGen", 44);
        let natlist = ix.insert_sort("QNatList", 45);
        let splitlist = ix.insert_sort("QSplitList", 46);
        let boxlist = ix.insert_sort("QBoxList", 47);
        let region = ix.insert_sort("QRegionAtom", 48);
        let certfam = ix.insert_sort("QCertFam", 49);
        let comblist = ix.insert_sort("QCertCombList", 50);
        // The deadline-table family's sorts (ids 70+
        // keep every existing sort id unchanged; their funs are
        // appended at the closure's end).
        let qjudgment = ix.insert_sort("QJudgment", 70);
        let qproof = ix.insert_sort("QProof", 71);
        let qsat = ix.insert_sort("QSat", 72);
        let qdeadline = ix.insert_sort("QDeadlineTable", 73);
        let e = SortKey::Elem;
        let g = SortKey::Ground;
        let mut ctr = 10u32;
        let mut fun = |name: &str, domain: DomainSig, codomain: SortKey| {
            ctr += 1;
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (QTSLCERT, ctr),
                relational: false,
                side_condition: false,
                domain,
                codomain: Some(codomain),
            });
        };
        fun(
            "qbagMk",
            record(&[("dim", g(Ground::Nat)), ("tokens", e(toklist))]),
            e(bag),
        );
        fun("qbtNil", DomainSig::Nullary, e(toklist));
        fun(
            "qbtCons",
            record(&[("head", e(ratlist)), ("tail", e(toklist))]),
            e(toklist),
        );
        fun("qrlNil", DomainSig::Nullary, e(ratlist));
        fun(
            "qrlCons",
            record(&[("head", g(Ground::Q)), ("tail", e(ratlist))]),
            e(ratlist),
        );
        // --- the ProbLog family's declarations ---
        fun(
            "qplogMk",
            record(&[
                ("clauses", e(plog_clauses)),
                ("coins", e(plog_coins)),
                ("dets", g(Ground::Shape)),
                ("facts", e(plog_facts)),
                ("query", g(Ground::Nat)),
            ]),
            e(plog_prog),
        );
        fun("qpcNil", DomainSig::Nullary, e(plog_coins));
        fun(
            "qpcCons",
            record(&[
                ("id", g(Ground::Nat)),
                ("prob", g(Ground::Q)),
                ("tail", e(plog_coins)),
            ]),
            e(plog_coins),
        );
        fun("qpfNil", DomainSig::Nullary, e(plog_facts));
        fun(
            "qpfCons",
            record(&[
                ("atom", g(Ground::Nat)),
                ("coin", g(Ground::Nat)),
                ("tail", e(plog_facts)),
            ]),
            e(plog_facts),
        );
        fun("qpkNil", DomainSig::Nullary, e(plog_clauses));
        fun(
            "qpkCons",
            record(&[
                ("body", g(Ground::Shape)),
                ("head", g(Ground::Nat)),
                ("tail", e(plog_clauses)),
            ]),
            e(plog_clauses),
        );
        fun("qpsNil", DomainSig::Nullary, e(plog_sets));
        fun(
            "qpsCons",
            record(&[("set", g(Ground::Shape)), ("tail", e(plog_sets))]),
            e(plog_sets),
        );
        // The domain-carrying coin constructor
        // (appended — existing chids unchanged).
        fun(
            "qpcConsD",
            record(&[
                ("dom", g(Ground::Nat)),
                ("id", g(Ground::Nat)),
                ("prob", g(Ground::Q)),
                ("tail", e(plog_coins)),
            ]),
            e(plog_coins),
        );
        // --- the carillon family's declarations ---
        // The unified-arena grid complex, the certificate box list,
        // and the region atoms (sorts declared above the closure;
        // QRatList is the existing sort). Appended — existing chids
        // unchanged.
        fun(
            "qgcMk",
            record(&[("dom", e(boxs)), ("tree", e(patchtree))]),
            e(gridcx),
        );
        fun(
            "qptLeaf",
            record(&[
                ("chart", e(chartref)),
                ("gens", e(genlist)),
                ("part", g(Ground::Shape)),
            ]),
            e(patchtree),
        );
        fun(
            "qptSplit",
            record(&[
                ("axis", g(Ground::Nat)),
                ("cut", g(Ground::Q)),
                ("hi", e(patchtree)),
                ("lo", e(patchtree)),
            ]),
            e(patchtree),
        );
        fun("qglNil", DomainSig::Nullary, e(genlist));
        fun(
            "qglCons",
            record(&[("gen", e(groupgen)), ("tail", e(genlist))]),
            e(genlist),
        );
        fun("qgenInterval", record(&[("cuts", e(ratlist))]), e(groupgen));
        fun(
            "qgenKuhn",
            record(&[("res", e(natlist)), ("splits", e(splitlist))]),
            e(groupgen),
        );
        fun("qchIdentity", DomainSig::Nullary, e(chartref));
        fun(
            "qchDigest",
            record(&[("sha256hex", g(Ground::Str))]),
            e(chartref),
        );
        fun("qbxNil", DomainSig::Nullary, e(boxlist));
        fun(
            "qbxCons",
            record(&[("head", e(boxs)), ("tail", e(boxlist))]),
            e(boxlist),
        );
        fun("qraBox", DomainSig::Unary(e(boxs)), e(region));
        fun(
            "qraSublevel",
            record(&[("cert", e(certfam)), ("thr", g(Ground::Q))]),
            e(region),
        );
        fun(
            "qraAffine",
            record(&[("row", e(comblist)), ("thr", g(Ground::Q))]),
            e(region),
        );
        // --- the compiled decision-term constructors (evaluator
        // leg; appended — existing chids unchanged). Record fields in
        // bytewise order, as everywhere in this fixture.
        fun(
            "qpdDecide",
            record(&[
                ("coin", g(Ground::Nat)),
                ("hi", e(plog_dectree)),
                ("lo", e(plog_dectree)),
            ]),
            e(plog_dectree),
        );
        fun(
            "qpdSwitch",
            record(&[("arms", e(plog_armlist)), ("dom", g(Ground::Nat))]),
            e(plog_dectree),
        );
        fun(
            "qpdAccept",
            record(&[("expl", g(Ground::Shape))]),
            e(plog_dectree),
        );
        fun(
            "qpdReject",
            record(&[("cut", g(Ground::Shape))]),
            e(plog_dectree),
        );
        fun("qpaNil", DomainSig::Nullary, e(plog_armlist));
        fun(
            "qpaCons",
            record(&[
                ("child", e(plog_dectree)),
                ("coin", g(Ground::Nat)),
                ("tail", e(plog_armlist)),
            ]),
            e(plog_armlist),
        );
        // --- the deadline-table family's declarations (the
        // deadline-table staging) --- the judgment/proof/satisfaction chain + the
        // rule node (sorts at ids 70+, declared above the closure;
        // appended — existing chids unchanged). QSat/sys and
        // QSat/spec land in the Qtsl-theory revision's sorts
        // (cross-revision references, as in the theory source).
        let system = qtslsys().sort("System").expect("qtslsys System sort");
        let spec = qtslsys().sort("Spec").expect("qtslsys Spec sort");
        fun(
            "QProof/concludes",
            DomainSig::Unary(e(qproof)),
            e(qjudgment),
        );
        fun("QSat/judgment", DomainSig::Unary(e(qsat)), e(qjudgment));
        fun("QSat/sys", DomainSig::Unary(e(qsat)), e(system));
        fun("QSat/spec", DomainSig::Unary(e(qsat)), e(spec));
        fun(
            "QDeadlineTable/proof",
            DomainSig::Unary(e(qdeadline)),
            e(qproof),
        );
        fun(
            "QDeadlineTable/table",
            DomainSig::Unary(e(qdeadline)),
            e(ratlist),
        );
        ix
    })
}

/// The synthetic Qtsl-theory revision's commit hash (the
/// System-composite block + the Poly sort — the system-spec family's
/// vocabulary).
pub const QTSLSYS: [u8; 32] = [0x75; 32];

/// The Qtsl-theory index: the Poly constructors and the
/// System-composite vocabulary, shapes transcribed from the theory
/// source (record fields in bytewise order — the wire argument
/// order):
///
/// ```text
/// pZero : () -> Poly
/// pTerm : [coeff: Q, expts: Shape, tail: Poly] -> Poly
/// SysMech : [mech: Mech] -> System
/// SysWire : [inner: SystemList, wiring: Wiring] -> System
/// mkWiring : [inner: IfaceList, outer: Iface] -> Wiring
/// mkPortEq : [a: PortPath, b: PortPath, wiring: Wiring] -> PortEq
/// ppInner : [port: Port, pos: Nat] -> PortPath
/// ppOuter : [port: Port] -> PortPath
/// mkIface : [invars: PortList, outvars: PortList] -> Iface
/// mkInterval : [hi: Q, lo: Q] -> Interval
/// Mech/iface, Manifest/{varnames,modes}, Transition/clock
/// mech_manifest / mode_{diffusion,noise,noise_spectrum,
///   diffusion_hypernet} / sys_transition   (relations, event 3)
/// tkRace [majorant: EnnRat] / tkDemonic [dwellMin: EnnRat] /
///   tkForced [dwell: Q] -> TrClock ; enFin [q: Q] / enInf -> EnnRat
/// (+ the nil/cons pairs of every list sort)
/// ```
///
/// The legacy slice (`Mech/manifest`, `Manifest/transitions`,
/// `Mode/{jumps,diffusion,noise}`,
/// `Transition/{forced,src,guard_slab,dst,reset_image}`, `mkJump`,
/// the trl/jl kits) is GONE: removed from the real theory at the
/// event-3 closure (the Transition former restructure), retained here
/// only until the carillon vocabulary refresh, and deleted with
/// it — a fixture redeclaring retired vocabulary would be the
/// shadowing hazard the pinned-identity rule names. The syswire
/// family binds the event-3 names; its derived-tier tooth is the
/// baked-vocab binding test in `tests/syswire.rs`, which no synthetic
/// decl can satisfy.
pub fn qtslsys() -> &'static TheoryIndex {
    static IX: OnceLock<TheoryIndex> = OnceLock::new();
    IX.get_or_init(|| {
        let mut ix = TheoryIndex::new(QTSLSYS);
        let mut ctr: u32 = 0;
        let mut next = || {
            ctr += 1;
            ctr
        };
        let poly = ix.insert_sort("Poly", next());
        let system = ix.insert_sort("System", next());
        let syslist = ix.insert_sort("SystemList", next());
        let wiring = ix.insert_sort("Wiring", next());
        let porteq = ix.insert_sort("PortEq", next());
        let portpath = ix.insert_sort("PortPath", next());
        let iface = ix.insert_sort("Iface", next());
        let ifacelist = ix.insert_sort("IfaceList", next());
        let port = ix.insert_sort("Port", next());
        let portlist = ix.insert_sort("PortList", next());
        let mech = ix.insert_sort("Mech", next());
        let manifest = ix.insert_sort("Manifest", next());
        let mode = ix.insert_sort("Mode", next());
        let modelist = ix.insert_sort("ModeList", next());
        let transition = ix.insert_sort("Transition", next());
        // (TransitionList/Jump/JumpList: retired with the legacy
        // slice — the event-3 theory has no such sorts.)
        let strlist = ix.insert_sort("StrList", next());
        let boxs = ix.insert_sort("Box", next());
        let interval = ix.insert_sort("Interval", next());
        let polyvec = ix.insert_sort("PolyVec", next());
        let noiselist = ix.insert_sort("NoiseList", next());
        // The spec-former sorts (explicit ids 60+
        // keep every existing sort id unchanged; their funs are
        // appended at the closure's end).
        let spec = ix.insert_sort("Spec", 60);
        let statef = ix.insert_sort("StateF", 61);
        let pathf = ix.insert_sort("PathF", 62);
        let stateflist = ix.insert_sort("StateFList", 63);
        let e = SortKey::Elem;
        let g = SortKey::Ground;
        let mut ctr2: u32 = 100;
        let mut fun = |name: &str, domain: DomainSig, codomain: SortKey| {
            ctr2 += 1;
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (QTSLSYS, ctr2),
                relational: false,
                side_condition: false,
                domain,
                codomain: Some(codomain),
            });
        };
        let cons = |h: SortKey, t: Chid| record(&[("head", h), ("tail", e(t))]);

        // Polynomials.
        fun("pZero", DomainSig::Nullary, e(poly));
        fun(
            "pTerm",
            record(&[
                ("coeff", g(Ground::Q)),
                ("expts", g(Ground::Shape)),
                ("tail", e(poly)),
            ]),
            e(poly),
        );

        // Interfaces.
        fun(
            "mkPort",
            record(&[("name", g(Ground::Str)), ("shape", g(Ground::Shape))]),
            e(port),
        );
        fun("ptNil", DomainSig::Nullary, e(portlist));
        fun("ptCons", cons(e(port), portlist), e(portlist));
        fun(
            "mkIface",
            record(&[("invars", e(portlist)), ("outvars", e(portlist))]),
            e(iface),
        );
        fun("ilNil", DomainSig::Nullary, e(ifacelist));
        fun("ilCons", cons(e(iface), ifacelist), e(ifacelist));

        // Wirings.
        fun(
            "mkWiring",
            record(&[("inner", e(ifacelist)), ("outer", e(iface))]),
            e(wiring),
        );
        fun(
            "mkPortEq",
            record(&[
                ("a", e(portpath)),
                ("b", e(portpath)),
                ("wiring", e(wiring)),
            ]),
            e(porteq),
        );
        fun(
            "ppInner",
            record(&[("port", e(port)), ("pos", g(Ground::Nat))]),
            e(portpath),
        );
        fun("ppOuter", record(&[("port", e(port))]), e(portpath));

        // Systems.
        fun("SysMech", record(&[("mech", e(mech))]), e(system));
        fun(
            "SysWire",
            record(&[("inner", e(syslist)), ("wiring", e(wiring))]),
            e(system),
        );
        fun("syNil", DomainSig::Nullary, e(syslist));
        fun("syCons", cons(e(system), syslist), e(syslist));

        // Mechanism content (entity attributes + the list sorts they
        // reach).
        fun("Mech/iface", DomainSig::Unary(e(mech)), e(iface));
        fun(
            "Manifest/varnames",
            DomainSig::Unary(e(manifest)),
            e(strlist),
        );
        fun("Manifest/modes", DomainSig::Unary(e(manifest)), e(modelist));
        fun("strNil", DomainSig::Nullary, e(strlist));
        fun("strCons", cons(g(Ground::Str), strlist), e(strlist));
        fun("mlNil", DomainSig::Nullary, e(modelist));
        fun("mlCons", cons(e(mode), modelist), e(modelist));
        // Mode/name + Mode/domain: current theory names (Mode entity
        // attributes), retained.
        fun("Mode/name", DomainSig::Unary(e(mode)), g(Ground::Str));
        fun("Mode/domain", DomainSig::Unary(e(mode)), e(boxs));
        fun("boxNil", DomainSig::Nullary, e(boxs));
        fun("boxCons", cons(e(interval), boxs), e(boxs));
        fun(
            "mkInterval",
            record(&[("hi", g(Ground::Q)), ("lo", g(Ground::Q))]),
            e(interval),
        );
        // The spec formers (appended — existing
        // chids unchanged). Shapes transcribed from Qtsl.geolog:
        // SProbGE : [p: Q, path: PathF] -> StateF (was SProb;
        //   renamed when the LE face landed)
        // SProbLE : [q: Q, path: PathF] -> StateF (the LE face)
        // PDeadline : [T: Q, arg: StateF, producerT: B] -> PathF
        // SAtomLE/SAtomGE : [c: Q, poly: Poly] -> StateF
        // SAnd/SOr : StateFList -> StateF ; SNot : StateF -> StateF
        fun("Spec/root", DomainSig::Unary(e(spec)), e(statef));
        fun("Spec/name", DomainSig::Unary(e(spec)), g(Ground::Str));
        fun(
            "SProbGE",
            record(&[("p", g(Ground::Q)), ("path", e(pathf))]),
            e(statef),
        );
        fun(
            "SProbLE",
            record(&[("path", e(pathf)), ("q", g(Ground::Q))]),
            e(statef),
        );
        fun(
            "PDeadline",
            record(&[
                ("T", g(Ground::Q)),
                ("arg", e(statef)),
                ("producerT", g(Ground::B)),
            ]),
            e(pathf),
        );
        fun("STrue", DomainSig::Nullary, e(statef));
        fun("SFalse", DomainSig::Nullary, e(statef));
        fun(
            "SAtomLE",
            record(&[("c", g(Ground::Q)), ("poly", e(poly))]),
            e(statef),
        );
        fun(
            "SAtomGE",
            record(&[("c", g(Ground::Q)), ("poly", e(poly))]),
            e(statef),
        );
        fun("SAnd", DomainSig::Unary(e(stateflist)), e(statef));
        fun("SOr", DomainSig::Unary(e(stateflist)), e(statef));
        fun("SNot", DomainSig::Unary(e(statef)), e(statef));
        fun("slNil", DomainSig::Nullary, e(stateflist));
        fun("slCons", cons(e(statef), stateflist), e(stateflist));
        // The event-3 System/Transition slice (appended — existing
        // chids unchanged). New sorts at explicit ids 70+ (60-63 are
        // the spec formers').
        let trclock = ix.insert_sort("TrClock", 70);
        let ennrat = ix.insert_sort("EnnRat", 71);
        let noisespec = ix.insert_sort("NoiseSpectrum", 72);
        let hypref = ix.insert_sort("HypernetRef", 73);
        let mut fun = |name: &str, domain: DomainSig, codomain: SortKey| {
            ctr2 += 1;
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (QTSLSYS, ctr2),
                relational: false,
                side_condition: false,
                domain,
                codomain: Some(codomain),
            });
        };
        fun(
            "Transition/clock",
            DomainSig::Unary(e(transition)),
            e(trclock),
        );
        fun("tkRace", record(&[("majorant", e(ennrat))]), e(trclock));
        fun("tkDemonic", record(&[("dwellMin", e(ennrat))]), e(trclock));
        fun("tkForced", record(&[("dwell", g(Ground::Q))]), e(trclock));
        // The carved-window wing (event 5 fixtures).
        // Bytewise field order: ceil < floor.
        fun(
            "tkCarved",
            record(&[("ceil", e(ennrat)), ("floor", g(Ground::Q))]),
            e(trclock),
        );
        fun("enFin", record(&[("q", g(Ground::Q))]), e(ennrat));
        fun("enInf", DomainSig::Nullary, e(ennrat));
        // Relations (record fields in bytewise order — the wire
        // argument order the loaders produce).
        let mut relf = |name: &str, domain: DomainSig| {
            ctr2 += 1;
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (QTSLSYS, ctr2),
                relational: true,
                side_condition: false,
                domain,
                codomain: None,
            });
        };
        relf(
            "mech_manifest",
            record(&[("manifest", e(manifest)), ("mech", e(mech))]),
        );
        relf(
            "mode_diffusion",
            record(&[("col", e(polyvec)), ("mode", e(mode))]),
        );
        relf(
            "mode_noise",
            record(&[("drivers", e(noiselist)), ("mode", e(mode))]),
        );
        relf(
            "mode_noise_spectrum",
            record(&[("mode", e(mode)), ("spectrum", e(noisespec))]),
        );
        relf(
            "mode_diffusion_hypernet",
            record(&[("mode", e(mode)), ("ref", e(hypref))]),
        );
        relf(
            "sys_transition",
            record(&[("sys", e(system)), ("tr", e(transition))]),
        );
        ix
    })
}

/// The Transition-former + bag-former revision's commit hash (the
/// trwf family's fixture vocabulary — a separate synthetic revision
/// so `qtslsys()`'s chids stay untouched; the provider's resolvers
/// sweep both).
pub const QTSLTR: [u8; 32] = [0x7B; 32];

/// The Transition-former index: the two content presentations, the
/// grain/clock attributes and their constructor kits, the scale
/// view's tagged mixture, and the bag former's relations. Shapes
/// transcribed from the Qtsl theory source (record fields in
/// bytewise order — the wire argument order).
pub fn qtsltr() -> &'static TheoryIndex {
    static IX: OnceLock<TheoryIndex> = OnceLock::new();
    IX.get_or_init(|| {
        let mut ix = TheoryIndex::new(QTSLTR);
        // Sorts shared with the system index are REUSED by chid (a
        // sort is its pinned identity; declaring a same-named sort
        // here would shadow under name resolution).
        let sys_ix = qtslsys();
        let system = sys_ix.sort("System").expect("qtslsys System sort");
        let mech = sys_ix.sort("Mech").expect("qtslsys Mech sort");
        let transition = sys_ix.sort("Transition").expect("qtslsys Transition sort");
        let poly = sys_ix.sort("Poly").expect("qtslsys Poly sort");
        let polyvec = sys_ix.sort("PolyVec").expect("qtslsys PolyVec sort");
        let boxs = sys_ix.sort("Box").expect("qtslsys Box sort");
        let interval = sys_ix.sort("Interval").expect("qtslsys Interval sort");
        let mut ctr: u32 = 0;
        let mut next = || {
            ctr += 1;
            ctr
        };
        let scaleview = ix.insert_sort("ScaleView", next());
        let branchlist = ix.insert_sort("StepBranchList", next());
        let stepres = ix.insert_sort("StepRes", next());
        let kernelcite = ix.insert_sort("KernelCite", next());
        // The clock kit lives in the system index since the event-3
        // refresh landed it there — REUSED by chid, never redeclared
        // (the same pinned-identity rule as the sorts above; a
        // same-named fun here would skew name resolution between the
        // provider's sweep and any fixture that emits rows).
        let _trclock = sys_ix.sort("TrClock").expect("qtslsys TrClock sort");
        let _ennrat = sys_ix.sort("EnnRat").expect("qtslsys EnnRat sort");
        let trgrain = ix.insert_sort("TrGrain", next());
        let selspec = ix.insert_sort("SelSpec", next());
        let ssl = ix.insert_sort("SelSpecList", next());
        let token = ix.insert_sort("Token", next());
        let bagloop = ix.insert_sort("BagLoop", next());
        let baglaw = ix.insert_sort("BagLaw", next());
        let e = SortKey::Elem;
        let g = SortKey::Ground;
        let mut ctr2: u32 = 100;
        let mut decl =
            |name: &str, relational: bool, domain: DomainSig, codomain: Option<SortKey>| {
                ctr2 += 1;
                ix.insert_fun(FunDecl {
                    name: name.to_string(),
                    chid: (QTSLTR, ctr2),
                    relational,
                    side_condition: false,
                    domain,
                    codomain,
                });
            };

        // The two content presentations (relations).
        decl(
            "tr_kernel",
            true,
            record(&[("kernel", e(kernelcite)), ("tr", e(transition))]),
            None,
        );
        decl(
            "tr_scale",
            true,
            record(&[("scale", e(scaleview)), ("tr", e(transition))]),
            None,
        );
        // The carved-window gate row (event 5 fixtures).
        // Bytewise field order: gate < tr; HypernetRef is qtslsys's
        // sort, reused by chid.
        let hypref = sys_ix
            .sort("HypernetRef")
            .expect("qtslsys HypernetRef sort");
        decl(
            "tr_dwell_gate",
            true,
            record(&[("gate", e(hypref)), ("tr", e(transition))]),
            None,
        );
        // The scale view and its tagged mixture.
        decl(
            "mkScaleView",
            false,
            record(&[("mix", e(branchlist)), ("rate", e(poly))]),
            Some(e(scaleview)),
        );
        decl("sbNil", false, DomainSig::Nullary, Some(e(branchlist)));
        decl(
            "sbCons",
            false,
            record(&[
                ("step", e(stepres)),
                ("tail", e(branchlist)),
                ("weight", g(Ground::Q)),
            ]),
            Some(e(branchlist)),
        );
        decl(
            "srNext",
            false,
            record(&[("image", e(boxs)), ("reset", e(polyvec))]),
            Some(e(stepres)),
        );
        decl("srStay", false, DomainSig::Nullary, Some(e(stepres)));
        decl("srCemetery", false, DomainSig::Nullary, Some(e(stepres)));
        decl("pvNil", false, DomainSig::Nullary, Some(e(polyvec)));
        decl(
            "pvCons",
            false,
            record(&[("head", e(poly)), ("tail", e(polyvec))]),
            Some(e(polyvec)),
        );

        // The exactly-one transition attributes + the clock kit.
        decl(
            "Transition/grain",
            false,
            DomainSig::Unary(e(transition)),
            Some(e(trgrain)),
        );
        // Grains.
        decl("grWhole", false, DomainSig::Nullary, Some(e(trgrain)));
        decl(
            "grVariant",
            false,
            record(&[("ix", g(Ground::Nat))]),
            Some(e(trgrain)),
        );
        decl(
            "grTuple",
            false,
            record(&[("pre", e(ssl))]),
            Some(e(trgrain)),
        );
        decl(
            "grPath",
            false,
            record(&[("inner", e(trgrain)), ("outer", e(trgrain))]),
            Some(e(trgrain)),
        );
        decl(
            "selMk",
            false,
            record(&[
                ("consume", g(Ground::Nat)),
                ("place", g(Ground::Nat)),
                ("read", g(Ground::Nat)),
            ]),
            Some(e(selspec)),
        );
        decl("sslNil", false, DomainSig::Nullary, Some(e(ssl)));
        decl(
            "sslCons",
            false,
            record(&[("head", e(selspec)), ("tail", e(ssl))]),
            Some(e(ssl)),
        );

        // The bag former.
        decl(
            "mech_bag_base",
            true,
            record(&[("base", e(system)), ("mech", e(mech))]),
            None,
        );
        decl(
            "mech_bag_capacity",
            true,
            record(&[("capacity", g(Ground::Nat)), ("mech", e(mech))]),
            None,
        );
        decl(
            "mech_bag_loop",
            true,
            record(&[("loop", e(bagloop)), ("mech", e(mech))]),
            None,
        );
        decl(
            "mech_bag_marking",
            true,
            record(&[
                ("count", g(Ground::Nat)),
                ("mech", e(mech)),
                ("token", e(token)),
            ]),
            None,
        );
        decl(
            "blCreate",
            false,
            record(&[
                ("delta", g(Ground::Nat)),
                ("id", g(Ground::Str)),
                ("law", e(baglaw)),
            ]),
            Some(e(bagloop)),
        );
        decl(
            "blDestroy",
            false,
            record(&[
                ("delta", g(Ground::Nat)),
                ("id", g(Ground::Str)),
                ("law", e(baglaw)),
            ]),
            Some(e(bagloop)),
        );
        decl("blGuard", false, DomainSig::Nullary, Some(e(baglaw)));

        // The interval constructor is qtslsys's; nothing to re-declare.
        let _ = interval;
        ix
    })
}

/// The Dtmc frame + bridge revision's commit hash.
pub const DTMC: [u8; 32] = [0xD7; 32];

/// The Dtmc-theory index: the discrete-kernel frame (models, states,
/// actions, outcome rows, init distribution, absorbing marks) and the
/// bridge species fields (`Mech/dtmc`, `Mech/dpolicy`, the policy
/// table). Shapes transcribed from `Dtmc.geolog`; `kprob`'s record
/// order matches the staged declaration (src, act, dst, rew — the
/// worked-instance rows' wire order), which the vocabulary builder
/// resolves BY NAME rather than assuming.
pub fn dtmc() -> &'static TheoryIndex {
    static IX: OnceLock<TheoryIndex> = OnceLock::new();
    IX.get_or_init(|| {
        let mut ix = TheoryIndex::new(DTMC);
        let dtmc_s = ix.insert_sort("Dtmc", 1);
        let dstate = ix.insert_sort("DState", 2);
        let dact = ix.insert_sort("DAct", 3);
        let dpolicy = ix.insert_sort("DPolicy", 4);
        let mech = qtslsys().sort("Mech").expect("qtslsys Mech sort");
        let e = SortKey::Elem;
        let g = SortKey::Ground;
        let mut ctr = 10u32;
        let mut fun =
            |name: &str, relational: bool, domain: DomainSig, codomain: Option<SortKey>| {
                ctr += 1;
                ix.insert_fun(FunDecl {
                    name: name.to_string(),
                    chid: (DTMC, ctr),
                    relational,
                    side_condition: false,
                    domain,
                    codomain,
                });
            };
        fun(
            "Dtmc/name",
            false,
            DomainSig::Unary(e(dtmc_s)),
            Some(g(Ground::Str)),
        );
        fun(
            "DState/dtmc",
            false,
            DomainSig::Unary(e(dstate)),
            Some(e(dtmc_s)),
        );
        fun(
            "DState/idx",
            false,
            DomainSig::Unary(e(dstate)),
            Some(g(Ground::Nat)),
        );
        fun("DState/absorbing", true, DomainSig::Unary(e(dstate)), None);
        fun(
            "DAct/dtmc",
            false,
            DomainSig::Unary(e(dact)),
            Some(e(dtmc_s)),
        );
        fun(
            "DAct/idx",
            false,
            DomainSig::Unary(e(dact)),
            Some(g(Ground::Nat)),
        );
        fun(
            "kprob",
            false,
            record(&[
                ("src", e(dstate)),
                ("act", e(dact)),
                ("dst", e(dstate)),
                ("rew", g(Ground::Q)),
            ]),
            Some(g(Ground::Q)),
        );
        fun(
            "kinit",
            false,
            record(&[("dtmc", e(dtmc_s)), ("state", e(dstate))]),
            Some(g(Ground::Q)),
        );
        fun(
            "Mech/dtmc",
            false,
            DomainSig::Unary(e(mech)),
            Some(e(dtmc_s)),
        );
        fun(
            "Mech/dpolicy",
            false,
            DomainSig::Unary(e(mech)),
            Some(e(dpolicy)),
        );
        fun(
            "DPolicy/dtmc",
            false,
            DomainSig::Unary(e(dpolicy)),
            Some(e(dtmc_s)),
        );
        fun(
            "DPolicy/horizon",
            false,
            DomainSig::Unary(e(dpolicy)),
            Some(g(Ground::Nat)),
        );
        fun(
            "pact",
            false,
            record(&[
                ("pol", e(dpolicy)),
                ("src", e(dstate)),
                ("t", g(Ground::Nat)),
            ]),
            Some(e(dact)),
        );
        ix
    })
}

/// The guarded-specification revision's commit hash (the guard
/// family's fixture vocabulary — a separate synthetic revision so the
/// existing indices' chids stay untouched). It carries the EVENT-4
/// spec-record generation: the renamed sorts (StatePred/PathPred, new
/// ForallSpec/StateObservable), the re-founded atoms (`SAtomLE {c, o}`
/// — where `qtslsys()` still declares the RETIRED StateF generation
/// for the deadline family's fixtures), the record relations, the
/// warrant routes, and the bag-wire/init-box subject content. The
/// guard resolvers are shadowing-tolerant by design (shape co-selects
/// beside the name), so both generations coexist in one sweep — which
/// is itself the fixture for that resolver property.
pub const QTSLGUARD: [u8; 32] = [0x7D; 32];

pub fn qtslguard() -> &'static TheoryIndex {
    static IX: OnceLock<TheoryIndex> = OnceLock::new();
    IX.get_or_init(|| {
        let mut ix = TheoryIndex::new(QTSLGUARD);
        let forall = ix.insert_sort("ForallSpec", 1);
        let statepred = ix.insert_sort("StatePred", 2);
        let spl = ix.insert_sort("StatePredList", 3);
        let stateobs = ix.insert_sort("StateObservable", 4);
        let pathpred = ix.insert_sort("PathPred", 5);
        let qrs = ix.insert_sort("QRegionSat", 6);
        let qfs = ix.insert_sort("QForallSat", 11);
        let slack = ix.insert_sort("Slack", 7);
        let existsspec = ix.insert_sort("ExistsSpec", 8);
        let attitude = ix.insert_sort("AttitudeSpec", 9);
        let pathobs = ix.insert_sort("PathObservable", 10);
        // Cross-revision anchors (as in the theory source: the record
        // cites the subject strata, the certificate stratum cites both).
        let sys_ix = qtslsys();
        let spec = sys_ix.sort("Spec").expect("qtslsys Spec sort");
        let system = sys_ix.sort("System").expect("qtslsys System sort");
        let mech = sys_ix.sort("Mech").expect("qtslsys Mech sort");
        let iface = sys_ix.sort("Iface").expect("qtslsys Iface sort");
        let poly = sys_ix.sort("Poly").expect("qtslsys Poly sort");
        let boxs = sys_ix.sort("Box").expect("qtslsys Box sort");
        let qsat = qtslcert().sort("QSat").expect("qtslcert QSat sort");
        let region = qtslcert()
            .sort("QRegionAtom")
            .expect("qtslcert QRegionAtom sort");
        let token = qtsltr().sort("Token").expect("qtsltr Token sort");
        let proof = stack().sort("Proof").expect("stack Proof sort");
        let e = SortKey::Elem;
        let g = SortKey::Ground;
        let mut ctr = 100u32;
        let mut fun = |name: &str, domain: DomainSig, codomain: SortKey| {
            ctr += 1;
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (QTSLGUARD, ctr),
                relational: false,
                side_condition: false,
                domain,
                codomain: Some(codomain),
            });
        };
        // The event-4 cap formers (record fields in bytewise order).
        fun("SInit", record(&[("arg", e(statepred))]), e(forall));
        fun(
            "SProbGE",
            record(&[("p", g(Ground::Q)), ("path", e(pathpred))]),
            e(forall),
        );
        fun(
            "SRegretLE",
            record(&[
                ("eps", g(Ground::Q)),
                ("pi", e(system)),
                ("ret", e(pathobs)),
            ]),
            e(forall),
        );
        fun(
            "SRegretLEMark",
            record(&[("eps", g(Ground::Q)), ("ret", e(pathobs))]),
            e(existsspec),
        );
        fun("STrue", DomainSig::Nullary, e(statepred));
        fun("SFalse", DomainSig::Nullary, e(statepred));
        fun(
            "SAtomLE",
            record(&[("c", g(Ground::Q)), ("o", e(stateobs))]),
            e(statepred),
        );
        fun(
            "SAtomGE",
            record(&[("c", g(Ground::Q)), ("o", e(stateobs))]),
            e(statepred),
        );
        fun("SAnd", DomainSig::Unary(e(spl)), e(statepred));
        fun("SOr", DomainSig::Unary(e(spl)), e(statepred));
        fun("SNot", DomainSig::Unary(e(statepred)), e(statepred));
        fun("slNil", DomainSig::Nullary, e(spl));
        fun(
            "slCons",
            record(&[("head", e(statepred)), ("tail", e(spl))]),
            e(spl),
        );
        fun("oPoly", record(&[("poly", e(poly))]), e(stateobs));
        fun("oInd", record(&[("arg", e(statepred))]), e(stateobs));
        fun("PAlways", DomainSig::Unary(e(statepred)), e(pathpred));
        fun("PNotPath", DomainSig::Unary(e(pathpred)), e(pathpred));
        // The holed-subject constructor (the seat-regret vocabulary's
        // System face).
        fun("SysHole", record(&[("iface", e(iface))]), e(system));
        // The region-satisfaction claim's region attribute.
        fun("QRegionSat/region", DomainSig::Unary(e(qrs)), e(region));
        // The forall-face warrant entity (event 6: the warrant seam
        // unified onto QForallSat — component/region intrinsic).
        fun("QForallSat/component", DomainSig::Unary(e(qfs)), e(forall));
        fun("QForallSat/region", DomainSig::Unary(e(qfs)), e(region));
        let _ = (slack, attitude); // field sorts below
                                   // Relations (record fields in bytewise order — wire order).
        let mut relf = |name: &str, domain: DomainSig| {
            ctr += 1;
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (QTSLGUARD, ctr),
                relational: true,
                side_condition: false,
                domain,
                codomain: None,
            });
        };
        relf(
            "spec_forall",
            record(&[("f", e(forall)), ("spec", e(spec))]),
        );
        relf(
            "spec_exists",
            record(&[("e", e(existsspec)), ("spec", e(spec))]),
        );
        relf(
            "spec_score",
            record(&[("h", e(attitude)), ("spec", e(spec))]),
        );
        relf(
            "spec_name",
            record(&[("name", g(Ground::Str)), ("spec", e(spec))]),
        );
        relf(
            "spec_iface",
            record(&[("iface", e(iface)), ("spec", e(spec))]),
        );
        relf(
            "spec_assume",
            record(&[("assume", e(statepred)), ("spec", e(spec))]),
        );
        relf(
            "spec_slack",
            record(&[("slack", e(slack)), ("spec", e(spec))]),
        );
        relf(
            "spec_or",
            record(&[("left", e(spec)), ("right", e(spec)), ("spec", e(spec))]),
        );
        relf(
            "spec_guard",
            record(&[("region", e(region)), ("spec", e(spec))]),
        );
        relf(
            "qsat_warrant",
            record(&[("sat", e(qsat)), ("warrant", e(qfs))]),
        );
        relf(
            "qsat_guard_warrant",
            record(&[("sat", e(qsat)), ("warrant", e(qfs))]),
        );
        relf("qsat_eval", record(&[("eval", e(proof)), ("sat", e(qsat))]));
        relf(
            "mech_bag_wire",
            record(&[
                ("mech", e(mech)),
                ("token", e(token)),
                ("wire", g(Ground::Nat)),
            ]),
        );
        relf(
            "mech_init_box",
            record(&[("box", e(boxs)), ("mech", e(mech))]),
        );
        ix
    })
}

/// The angelic-selection revision's commit hash (the asel family's
/// fixture vocabulary — a separate synthetic revision, append-only:
/// every existing index's chids stay untouched). It carries the
/// angelic block (`ASelKind`/`ASelWitness`/`ASelCell`, the two slot
/// relations) plus the EVENT-6 face-typed compiled verdict form
/// (`QVerdictForm`/`qvfMk {exists_face, forall_face}`, the
/// `QExistsEntry`/`qxeMk` bridge, both list spines, `qsat_verdict`)
/// and the zeno-budget attachment — cross-revision anchors as in the
/// theory source (System/Transition/Mode/Box from `qtslsys`, QSat +
/// QRegionAtom from `qtslcert`, QRegionSat/QForallSat/ExistsSpec from
/// `qtslguard`).
pub const QTSLASEL: [u8; 32] = [0xA5; 32];

pub fn qtslasel() -> &'static TheoryIndex {
    static IX: OnceLock<TheoryIndex> = OnceLock::new();
    IX.get_or_init(|| {
        let mut ix = TheoryIndex::new(QTSLASEL);
        let aselkind = ix.insert_sort("ASelKind", 1);
        let aselwit = ix.insert_sort("ASelWitness", 2);
        let aselcell = ix.insert_sort("ASelCell", 3);
        let verdictform = ix.insert_sort("QVerdictForm", 4);
        let qxelist = ix.insert_sort("QExistsEntryList", 5);
        let crossbudget = ix.insert_sort("CrossBudget", 6);
        let qxe = ix.insert_sort("QExistsEntry", 7);
        let qfslist = ix.insert_sort("QForallSatList", 8);
        let sys_ix = qtslsys();
        let system = sys_ix.sort("System").expect("qtslsys System sort");
        let transition = sys_ix.sort("Transition").expect("qtslsys Transition sort");
        let mode = sys_ix.sort("Mode").expect("qtslsys Mode sort");
        let boxs = sys_ix.sort("Box").expect("qtslsys Box sort");
        let cert_ix = qtslcert();
        let qsat = cert_ix.sort("QSat").expect("qtslcert QSat sort");
        let region = cert_ix
            .sort("QRegionAtom")
            .expect("qtslcert QRegionAtom sort");
        let guard_ix = qtslguard();
        let qrs = guard_ix
            .sort("QRegionSat")
            .expect("qtslguard QRegionSat sort");
        let qfs = guard_ix
            .sort("QForallSat")
            .expect("qtslguard QForallSat sort");
        let existsspec = guard_ix
            .sort("ExistsSpec")
            .expect("qtslguard ExistsSpec sort");
        let e = SortKey::Elem;
        let g = SortKey::Ground;
        let mut ctr = 100u32;
        let mut fun = |name: &str, domain: DomainSig, codomain: SortKey| {
            ctr += 1;
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (QTSLASEL, ctr),
                relational: false,
                side_condition: false,
                domain,
                codomain: Some(codomain),
            });
        };
        fun("askDwell", DomainSig::Nullary, e(aselkind));
        fun("askRelay", DomainSig::Nullary, e(aselkind));
        fun("ASelWitness/sys", DomainSig::Unary(e(aselwit)), e(system));
        fun(
            "ASelWitness/eps",
            DomainSig::Unary(e(aselwit)),
            g(Ground::Q),
        );
        fun("ASelWitness/reach", DomainSig::Unary(e(aselwit)), e(qrs));
        fun("ASelCell/wit", DomainSig::Unary(e(aselcell)), e(aselwit));
        fun("ASelCell/dom", DomainSig::Unary(e(aselcell)), e(boxs));
        fun("ASelCell/mode", DomainSig::Unary(e(aselcell)), e(mode));
        fun("ASelCell/kind", DomainSig::Unary(e(aselcell)), e(aselkind));
        fun(
            "ASelCell/choice",
            DomainSig::Unary(e(aselcell)),
            e(transition),
        );
        fun(
            "qvfMk",
            record(&[("exists_face", e(qxelist)), ("forall_face", e(qfslist))]),
            e(verdictform),
        );
        fun(
            "qxeMk",
            record(&[("e", e(existsspec)), ("region", e(region))]),
            e(qxe),
        );
        fun("qxeNil", DomainSig::Nullary, e(qxelist));
        fun(
            "qxeCons",
            record(&[("head", e(qxe)), ("tail", e(qxelist))]),
            e(qxelist),
        );
        fun("qfsNil", DomainSig::Nullary, e(qfslist));
        fun(
            "qfsCons",
            record(&[("head", e(qfs)), ("tail", e(qfslist))]),
            e(qfslist),
        );
        let mut relf = |name: &str, domain: DomainSig| {
            ctr += 1;
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (QTSLASEL, ctr),
                relational: true,
                side_condition: false,
                domain,
                codomain: None,
            });
        };
        relf(
            "asel_exit",
            record(&[("cell", e(aselcell)), ("tr", e(transition))]),
        );
        relf(
            "asel_warrant",
            record(&[("mark", e(qrs)), ("wit", e(aselwit))]),
        );
        relf(
            "qsat_verdict",
            record(&[("form", e(verdictform)), ("sat", e(qsat))]),
        );
        relf(
            "qsat_zeno_budget",
            record(&[
                ("cb", e(crossbudget)),
                ("pos", g(Ground::Nat)),
                ("sat", e(qsat)),
            ]),
        );
        ix
    })
}

/// The kernel-citation circuit revision's commit hash (the circuit
/// family's fixture vocabulary — a separate synthetic revision,
/// append-only: every existing index's chids stay untouched). It
/// declares only the two constructors the store-seam port needs
/// beyond what the other indices already carry — `mkKernelCite` over
/// qtsltr's KernelCite and `hnDigest` over qtslsys's HypernetRef
/// (cross-revision references BY CHID, as in the theory source);
/// SysMech / grWhole / `Transition/grain` / tr_kernel /
/// mech_init_box / the Box kit all resolve from the existing indices.
pub const QTSLCIRC: [u8; 32] = [0xC1; 32];

pub fn qtslcirc() -> &'static TheoryIndex {
    static IX: OnceLock<TheoryIndex> = OnceLock::new();
    IX.get_or_init(|| {
        let mut ix = TheoryIndex::new(QTSLCIRC);
        let sys_ix = qtslsys();
        let hypref = sys_ix
            .sort("HypernetRef")
            .expect("qtslsys HypernetRef sort");
        let boxs = sys_ix.sort("Box").expect("qtslsys Box sort");
        let kernelcite = qtsltr().sort("KernelCite").expect("qtsltr KernelCite sort");
        let e = SortKey::Elem;
        let g = SortKey::Ground;
        let mut ctr = 100u32;
        let mut fun = |name: &str, domain: DomainSig, codomain: SortKey| {
            ctr += 1;
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (QTSLCIRC, ctr),
                relational: false,
                side_condition: false,
                domain,
                codomain: Some(codomain),
            });
        };
        // hnDigest : {sha256hex: Str} -> HypernetRef.
        fun(
            "hnDigest",
            record(&[("sha256hex", g(Ground::Str))]),
            e(hypref),
        );
        // mkKernelCite : {cemetery: Nat, hypernet: HypernetRef,
        //                 image: Box, next: Nat, noise: Shape,
        //                 stay: Nat} -> KernelCite (fields bytewise,
        // matching the theory source's own order).
        fun(
            "mkKernelCite",
            record(&[
                ("cemetery", g(Ground::Nat)),
                ("hypernet", e(hypref)),
                ("image", e(boxs)),
                ("next", g(Ground::Nat)),
                ("noise", g(Ground::Shape)),
                ("stay", g(Ground::Nat)),
            ]),
            e(kernelcite),
        );
        ix
    })
}

/// The marks-node vocabulary (the markflow family's
/// fixture revision — a separate synthetic revision, append-only:
/// every existing index's chids stay untouched). It declares the
/// QWireComposeMarks block per the event-5 theory source — the node's
/// ten attributes, the QSatList/QSpecList/QProofList/QCarveList/
/// QDiagList spines, the QDiagCert pair, and the closed DiagKind
/// genus — anchoring System/Wiring/PortPath/Spec/HypernetRef in
/// qtslsys, QSat/QProof/QRatList in qtslcert, and the BL `Proof`
/// leaf sort in the stack (cross-revision references by chid, as in
/// the theory source).
pub const QTSLMKW: [u8; 32] = [0x3B; 32];

pub fn qtslmkw() -> &'static TheoryIndex {
    static IX: OnceLock<TheoryIndex> = OnceLock::new();
    IX.get_or_init(|| {
        let mut ix = TheoryIndex::new(QTSLMKW);
        let node = ix.insert_sort("QWireComposeMarks", 1);
        let qsatlist = ix.insert_sort("QSatList", 2);
        let cert = ix.insert_sort("QWireCert", 3);
        let qspeclist = ix.insert_sort("QSpecList", 4);
        let qprooflist = ix.insert_sort("QProofList", 5);
        let qcarvelist = ix.insert_sort("QCarveList", 6);
        let qdiaglist = ix.insert_sort("QDiagList", 7);
        let qdiagcert = ix.insert_sort("QDiagCert", 8);
        let diagkind = ix.insert_sort("DiagKind", 9);
        let sys_ix = qtslsys();
        let wiring = sys_ix.sort("Wiring").expect("qtslsys Wiring sort");
        let portpath = sys_ix.sort("PortPath").expect("qtslsys PortPath sort");
        let spec = sys_ix.sort("Spec").expect("qtslsys Spec sort");
        let hypref = sys_ix
            .sort("HypernetRef")
            .expect("qtslsys HypernetRef sort");
        let qsat = qtslcert().sort("QSat").expect("qtslcert QSat sort");
        let qproof = qtslcert().sort("QProof").expect("qtslcert QProof sort");
        let qratlist = qtslcert().sort("QRatList").expect("qtslcert QRatList sort");
        let proof = stack().sort("Proof").expect("stack Proof sort");
        let e = SortKey::Elem;
        let g = SortKey::Ground;
        let mut ctr = 100u32;
        let mut fun = |name: &str, domain: DomainSig, codomain: SortKey| {
            ctr += 1;
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (QTSLMKW, ctr),
                relational: false,
                side_condition: false,
                domain,
                codomain: Some(codomain),
            });
        };
        // The node's ten attributes (theory source order).
        fun(
            "QWireComposeMarks/proof",
            DomainSig::Unary(e(node)),
            e(qproof),
        );
        fun(
            "QWireComposeMarks/components",
            DomainSig::Unary(e(node)),
            e(qsatlist),
        );
        fun(
            "QWireComposeMarks/wirecert",
            DomainSig::Unary(e(node)),
            e(cert),
        );
        fun(
            "QWireComposeMarks/latency_rows",
            DomainSig::Unary(e(node)),
            e(qprooflist),
        );
        fun(
            "QWireComposeMarks/schedule",
            DomainSig::Unary(e(node)),
            e(qratlist),
        );
        fun(
            "QWireComposeMarks/carves",
            DomainSig::Unary(e(node)),
            e(qcarvelist),
        );
        fun(
            "QWireComposeMarks/carve_rows",
            DomainSig::Unary(e(node)),
            e(qprooflist),
        );
        fun(
            "QWireComposeMarks/diagonal_rows",
            DomainSig::Unary(e(node)),
            e(qdiaglist),
        );
        fun(
            "QWireComposeMarks/entailment",
            DomainSig::Unary(e(node)),
            e(proof),
        );
        fun(
            "QWireComposeMarks/wellposedness",
            DomainSig::Unary(e(node)),
            e(qprooflist),
        );
        // The cited certificate's read surface.
        fun("QWireCert/wiring", DomainSig::Unary(e(cert)), e(wiring));
        fun(
            "QWireCert/premises",
            DomainSig::Unary(e(cert)),
            e(qspeclist),
        );
        // Spines (record fields in bytewise order).
        fun("qsatNil", DomainSig::Nullary, e(qsatlist));
        fun(
            "qsatCons",
            record(&[("head", e(qsat)), ("tail", e(qsatlist))]),
            e(qsatlist),
        );
        fun("qspecNil", DomainSig::Nullary, e(qspeclist));
        fun(
            "qspecCons",
            record(&[("head", e(spec)), ("tail", e(qspeclist))]),
            e(qspeclist),
        );
        fun("qplNil", DomainSig::Nullary, e(qprooflist));
        fun(
            "qplCons",
            record(&[("head", e(proof)), ("tail", e(qprooflist))]),
            e(qprooflist),
        );
        fun("qcvNil", DomainSig::Nullary, e(qcarvelist));
        fun(
            "qcvCons",
            record(&[
                ("gate", e(hypref)),
                ("tail", e(qcarvelist)),
                ("wire", e(portpath)),
            ]),
            e(qcarvelist),
        );
        fun("qdgNil", DomainSig::Nullary, e(qdiaglist));
        fun(
            "qdgCons",
            record(&[("head", e(qdiagcert)), ("tail", e(qdiaglist))]),
            e(qdiaglist),
        );
        fun(
            "QDiagCert/kind",
            DomainSig::Unary(e(qdiagcert)),
            e(diagkind),
        );
        fun(
            "QDiagCert/rows",
            DomainSig::Unary(e(qdiagcert)),
            e(qprooflist),
        );
        // The closed diagonal-species genus.
        fun("dgPoint", DomainSig::Nullary, e(diagkind));
        fun("dgEnum", DomainSig::Nullary, e(diagkind));
        fun("dgContract", DomainSig::Nullary, e(diagkind));
        fun("dgConvex", DomainSig::Nullary, e(diagkind));
        fun("dgMonotone", DomainSig::Nullary, e(diagkind));
        let _ = g;
        ix
    })
}

/// The composition-node vocabulary (the causality-walk
/// family's fixture revision — a separate synthetic revision,
/// append-only: every existing index's chids stay untouched). It
/// declares the QWireCompose block per the theory source — the node's
/// five attributes and the QNatList rank spine — anchoring
/// Wiring/PortPath in qtslsys, QNatList/QProof in qtslcert, and
/// QSatList/QWireCert/QSpecList/QProofList in qtslmkw
/// (cross-revision references by chid, as in the theory source,
/// where the whole block rides one omnibus).
pub const QTSLWC: [u8; 32] = [0x57; 32];

pub fn qtslwc() -> &'static TheoryIndex {
    static IX: OnceLock<TheoryIndex> = OnceLock::new();
    IX.get_or_init(|| {
        let mut ix = TheoryIndex::new(QTSLWC);
        let node = ix.insert_sort("QWireCompose", 1);
        let mkw_ix = qtslmkw();
        let qsatlist = mkw_ix.sort("QSatList").expect("qtslmkw QSatList sort");
        let cert = mkw_ix.sort("QWireCert").expect("qtslmkw QWireCert sort");
        let qprooflist = mkw_ix.sort("QProofList").expect("qtslmkw QProofList sort");
        let natlist = qtslcert().sort("QNatList").expect("qtslcert QNatList sort");
        let qproof = qtslcert().sort("QProof").expect("qtslcert QProof sort");
        let e = SortKey::Elem;
        let g = SortKey::Ground;
        let mut ctr = 100u32;
        let mut fun = |name: &str, domain: DomainSig, codomain: SortKey| {
            ctr += 1;
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (QTSLWC, ctr),
                relational: false,
                side_condition: false,
                domain,
                codomain: Some(codomain),
            });
        };
        // The node's five attributes (theory source order).
        fun("QWireCompose/proof", DomainSig::Unary(e(node)), e(qproof));
        fun(
            "QWireCompose/components",
            DomainSig::Unary(e(node)),
            e(qsatlist),
        );
        fun("QWireCompose/wirecert", DomainSig::Unary(e(node)), e(cert));
        fun("QWireCompose/ranks", DomainSig::Unary(e(node)), e(natlist));
        fun(
            "QWireCompose/wellposedness",
            DomainSig::Unary(e(node)),
            e(qprooflist),
        );
        // The rank spine (heads are Nat GROUND literals; QNatList has
        // no constructors in any other synthetic index, so these are
        // the sweep's sole qnl pair — no cross-index ambiguity).
        fun("qnlNil", DomainSig::Nullary, e(natlist));
        fun(
            "qnlCons",
            record(&[("head", g(Ground::Nat)), ("tail", e(natlist))]),
            e(natlist),
        );
        ix
    })
}

/// The LRA-battery revision's commit hash (the avgbattery
/// family's fixture vocabulary — a separate synthetic revision,
/// append-only: every existing index's chids stay untouched). It
/// declares the QAvgBattery block per the baked e6 theory source —
/// the node's ten attributes (the `lowbounds` spelling) and the
/// `QInvScope` scope-warrant sort — plus the Return-stratum formers
/// the walk's face recompute reads (`SReturnLE`/`SReturnGE` into
/// qtslguard's ForallSpec; `poAvg` — and `poSup`, the wrong-former
/// drill's sibling — into qtslguard's PathObservable), anchoring
/// StatePred/StateObservable in `qtslguard`, QSat/QProof/QCertFam in
/// `qtslcert`, QProofList in `qtslmkw`, and the BL `Proof` leaf sort
/// in `stack` (cross-revision references by chid, as in the theory
/// source, where the whole block rides one omnibus).
pub const QTSLAVG: [u8; 32] = [0xAB; 32];

pub fn qtslavg() -> &'static TheoryIndex {
    static IX: OnceLock<TheoryIndex> = OnceLock::new();
    IX.get_or_init(|| {
        let mut ix = TheoryIndex::new(QTSLAVG);
        let node = ix.insert_sort("QAvgBattery", 1);
        let scope = ix.insert_sort("QInvScope", 2);
        let guard_ix = qtslguard();
        let statepred = guard_ix
            .sort("StatePred")
            .expect("qtslguard StatePred sort");
        let stateobs = guard_ix
            .sort("StateObservable")
            .expect("qtslguard StateObservable sort");
        let pathobs = guard_ix
            .sort("PathObservable")
            .expect("qtslguard PathObservable sort");
        let forall = guard_ix
            .sort("ForallSpec")
            .expect("qtslguard ForallSpec sort");
        let qproof = qtslcert().sort("QProof").expect("qtslcert QProof sort");
        let certfam = qtslcert().sort("QCertFam").expect("qtslcert QCertFam sort");
        let qprooflist = qtslmkw()
            .sort("QProofList")
            .expect("qtslmkw QProofList sort");
        let proof = stack().sort("Proof").expect("stack Proof sort");
        let e = SortKey::Elem;
        let g = SortKey::Ground;
        let mut ctr = 100u32;
        let mut fun = |name: &str, domain: DomainSig, codomain: SortKey| {
            ctr += 1;
            ix.insert_fun(FunDecl {
                name: name.to_string(),
                chid: (QTSLAVG, ctr),
                relational: false,
                side_condition: false,
                domain,
                codomain: Some(codomain),
            });
        };
        // The node's ten attributes (theory source order; e6
        // `lowbounds` spelling).
        fun("QAvgBattery/proof", DomainSig::Unary(e(node)), e(qproof));
        fun("QAvgBattery/gain", DomainSig::Unary(e(node)), g(Ground::Q));
        fun("QAvgBattery/arg", DomainSig::Unary(e(node)), e(statepred));
        fun("QAvgBattery/cert", DomainSig::Unary(e(node)), e(certfam));
        fun(
            "QAvgBattery/drifts",
            DomainSig::Unary(e(node)),
            e(qprooflist),
        );
        fun(
            "QAvgBattery/guards",
            DomainSig::Unary(e(node)),
            e(qprooflist),
        );
        fun(
            "QAvgBattery/lowbounds",
            DomainSig::Unary(e(node)),
            e(qprooflist),
        );
        fun(
            "QAvgBattery/nonnegs",
            DomainSig::Unary(e(node)),
            e(qprooflist),
        );
        fun("QAvgBattery/tie", DomainSig::Unary(e(node)), e(proof));
        fun(
            "QAvgBattery/scope_warrant",
            DomainSig::Unary(e(node)),
            e(scope),
        );
        // The Return-stratum formers (record fields in bytewise
        // order — the wire argument order).
        fun(
            "SReturnLE",
            record(&[("hi", g(Ground::Q)), ("ret", e(pathobs))]),
            e(forall),
        );
        fun(
            "SReturnGE",
            record(&[("lo", g(Ground::Q)), ("ret", e(pathobs))]),
            e(forall),
        );
        fun("poAvg", record(&[("o", e(stateobs))]), e(pathobs));
        // The non-Cesàro sibling (the wrong-former drill decides
        // FALSE against a resolvable row, as on the real closures).
        fun("poSup", record(&[("o", e(stateobs))]), e(pathobs));
        ix
    })
}

/// The synthetic sweep, in the provider's index order — shared by the
/// static storeless [`provider`] and by tests that construct their
/// own (e.g. a store-attached one).
pub fn sweep_indices() -> Vec<&'static TheoryIndex> {
    vec![
        stack(),
        qtslcert(),
        qtslsys(),
        dtmc(),
        qtsltr(),
        qtslguard(),
        qtslasel(),
        qtslcirc(),
        qtslmkw(),
        qtslwc(),
        qtslavg(),
    ]
}

/// The provider under test, built once over the synthetic indices.
pub fn provider() -> &'static QtslGroundProvider {
    static P: OnceLock<QtslGroundProvider> = OnceLock::new();
    P.get_or_init(|| {
        let vocab = QtslVocab::build(&sweep_indices());
        assert!(vocab.bl.is_some(), "applicability vocabulary resolves");
        assert!(vocab.bagcanon.is_some(), "bag vocabulary resolves");
        assert!(vocab.mask.is_some(), "mask vocabulary resolves");
        assert!(
            vocab.problog.is_some(),
            "problog vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.problog.as_ref().is_some_and(|v| v.has_compiled()),
            "problog compiled decision-term vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.polycanon.is_some(),
            "poly-canonicality vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.syswire.is_some(),
            "system-spec vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.barycoord.is_some(),
            "barycentric vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.cellapp.is_some(),
            "cell-application vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.lattice.is_some(),
            "block-lattice vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.enclosure.is_some(),
            "enclosure vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.carillon.is_some(),
            "carillon vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.surgery.is_some(),
            "surgery (CtxPath) vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.promise.is_some(),
            "promise (PPromise) vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.subdivide.is_some(),
            "subdivision (PSubdivide) vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.deadline.is_some(),
            "deadline-table vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.trwf.is_some(),
            "transition/bag well-formedness vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.guard.is_some(),
            "guarded-specification vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.asel.is_some(),
            "angelic-selection vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.circuit.is_some(),
            "kernel-citation circuit vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.gatescalar.is_some(),
            "gate-scalar vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.nnform.is_some(),
            "NN conclusion-form (ReLU application) vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.contract.is_some(),
            "semiring-cell (contract) vocabulary resolves: {:?}",
            vocab.notes
        );
        assert!(
            vocab.avgbattery.is_some(),
            "LRA-battery (QAvgBattery) vocabulary resolves: {:?}",
            vocab.notes
        );
        QtslGroundProvider::new(vec![REV], vocab)
    })
}

/// Evaluate a claimed relation by name through the full evaluation
/// path (cells + row context in, verdict out), rendered
/// result-shaped: `Holds`/`Fails` → `Ok`, `Refused` → `Err(reason)`.
pub fn ev(name: &str, args: &[&geolog_envelope::Value], rows: &CertRows) -> Result<bool, String> {
    let p = provider();
    let local = p
        .local_by_name(name)
        .unwrap_or_else(|| panic!("`{name}` claimed"));
    let cells: Vec<Vec<u8>> = args
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

/// `ev` over element arguments (local refs).
pub fn ev_elems(name: &str, elems: &[u32], rows: &CertRows) -> Result<bool, String> {
    use geolog_envelope::{ElemRef, Value};
    let vals: Vec<Value> = elems
        .iter()
        .map(|e| Value::Ref(ElemRef::Local(*e)))
        .collect();
    let refs: Vec<&Value> = vals.iter().collect();
    ev(name, &refs, rows)
}
