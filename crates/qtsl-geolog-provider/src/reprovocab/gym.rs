//! The gym deadline-table reproduction vocabulary (staged-chid pins):
//! the staged Qtsl/QtslCert/Dtmc revision chids and a CURATED SLICE of
//! their declarations — exactly what the certified-Gymnasium hitting
//! corpus's sealed certificates reference (the exact and dyadic
//! deadline-table lanes), what the provider's deadline vocabulary
//! builder demands, and the claimed relation (`qtsl_deadline_table`).
//!
//! Like [`super::bl`] (and unlike [`super::fluid_v0`]'s synthetic
//! revision), these constants pin REAL staged theory commits — the
//! same chain the deadline-table rule node's worked instance was
//! written against. The pinned-contract trust posture is unchanged:
//! the checker resolves against these constants, never against
//! anything a certificate carries. Cross-checks, stated honestly:
//!
//! - the producer (`gymdp glc`, mtk) duplicates the same pins as
//!   generated constants; the shared pins fixture
//!   (`tests/fixtures/gym_v0_pins.txt`, byte-identical in both repos)
//!   is the cross-repo tie, and the [`tests`] below assert this
//!   slice matches it entry for entry;
//! - a wrong counter or shape here cannot pass silently: the deadline
//!   walk recomputes every obligation from resolved rows, so a
//!   misbinding surfaces as refusals over the whole corpus.
//!
//! GENERATED: the declaration table below is emitted from the staged
//! chain by the vocabulary generator — regenerate, never hand-edit
//! (the staged chain moving = a NEW vocabulary version; artifacts in
//! the wild dep the old chids forever).

use crate::theory::{DomainSig, FunDecl, Ground, SortKey, TheoryIndex};

/// The obligation roster of the gym v0 vocabulary: one relation,
/// enumerated by the checker from the certificate's own
/// `QDeadlineTable` nodes (never claimed by the certificate).
pub const GYM_V0_OBLIGATIONS: [&str; 1] = ["qtsl_deadline_table"];

// GENERATED from the staged Qtsl/QtslCert/Dtmc theory chain — a curated
// slice: exactly the declarations the deadline-table certificate corpus
// references, the declarations the provider's deadline vocabulary builder
// demands, and the claimed relation. Chids are the staged revisions' own
// (commit, op counter) — regenerate (never hand-edit) when the staged
// chain moves.

pub const GYM_QTSL_V0_REV: [u8; 32] = [
    0xcc, 0x2f, 0x14, 0xfd, 0x5b, 0x57, 0x58, 0x73, 0x6f, 0x29, 0xf6, 0x80, 0xe2, 0xc8, 0x68, 0xd9,
    0xaa, 0xdd, 0x9a, 0x52, 0x0c, 0xbd, 0xa0, 0xfd, 0x1f, 0x54, 0xb4, 0xbd, 0x0d, 0xca, 0xba, 0x30,
];
pub const GYM_QTSLCERT_V0_REV: [u8; 32] = [
    0xd7, 0xd4, 0x53, 0x90, 0x7e, 0xee, 0xc1, 0x9a, 0x15, 0xfd, 0x3b, 0xb8, 0xe7, 0x72, 0x35, 0x3e,
    0x6f, 0xa4, 0x65, 0x41, 0x10, 0xd2, 0xbf, 0x00, 0x63, 0x68, 0x50, 0x7f, 0x62, 0xd2, 0xe3, 0x1a,
];
pub const GYM_DTMC_V0_REV: [u8; 32] = [
    0x92, 0x1e, 0x74, 0x70, 0xb6, 0xf7, 0x8d, 0x37, 0x15, 0xf0, 0x6b, 0x85, 0x9c, 0xa8, 0x44, 0x65,
    0x7c, 0xa0, 0xd5, 0x56, 0x5a, 0x8e, 0x26, 0x64, 0x1d, 0x46, 0xbf, 0xbd, 0xd1, 0x2a, 0xab, 0x53,
];

//SORT GYM_DTMC_V0_REV 2 DAct
//FUN GYM_DTMC_V0_REV 10 DAct/dtmc rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV,2))) codomain=SortKey::Elem((GYM_DTMC_V0_REV,0))
//FUN GYM_DTMC_V0_REV 11 DAct/idx rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV,2))) codomain=SortKey::Ground(Ground::Nat)
//FUN GYM_DTMC_V0_REV 12 DAct/name rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV,2))) codomain=SortKey::Ground(Ground::Str)
//SORT GYM_DTMC_V0_REV 3 DPolicy
//FUN GYM_DTMC_V0_REV 17 DPolicy/dtmc rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV,3))) codomain=SortKey::Elem((GYM_DTMC_V0_REV,0))
//FUN GYM_DTMC_V0_REV 18 DPolicy/horizon rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV,3))) codomain=SortKey::Ground(Ground::Nat)
//FUN GYM_DTMC_V0_REV 16 DPolicy/name rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV,3))) codomain=SortKey::Ground(Ground::Str)
//SORT GYM_DTMC_V0_REV 1 DState
//FUN GYM_DTMC_V0_REV 9 DState/absorbing rel=true side=false domain=DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV,1))) codomain=-
//FUN GYM_DTMC_V0_REV 7 DState/dtmc rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV,1))) codomain=SortKey::Elem((GYM_DTMC_V0_REV,0))
//FUN GYM_DTMC_V0_REV 8 DState/idx rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV,1))) codomain=SortKey::Ground(Ground::Nat)
//SORT GYM_DTMC_V0_REV 0 Dtmc
//FUN GYM_DTMC_V0_REV 6 Dtmc/name rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV,0))) codomain=SortKey::Ground(Ground::Str)
//SORT GYM_QTSL_V0_REV 30 Iface
//SORT GYM_QTSL_V0_REV 31 IfaceList
//SORT GYM_QTSL_V0_REV 33 Mech
//FUN GYM_DTMC_V0_REV 20 Mech/dpolicy rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV,33))) codomain=SortKey::Elem((GYM_DTMC_V0_REV,3))
//FUN GYM_DTMC_V0_REV 15 Mech/dtmc rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV,33))) codomain=SortKey::Elem((GYM_DTMC_V0_REV,0))
//FUN GYM_QTSL_V0_REV 156 Mech/iface rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV,33))) codomain=SortKey::Elem((GYM_QTSL_V0_REV,30))
//FUN GYM_QTSL_V0_REV 155 Mech/name rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV,33))) codomain=SortKey::Ground(Ground::Str)
//FUN GYM_QTSL_V0_REV 76 PDeadline rel=false side=false domain=DomainSig::Record(vec![("T".to_string(),SortKey::Ground(Ground::Q)),("arg".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,1))),("producerT".to_string(),SortKey::Ground(Ground::B))]) codomain=SortKey::Elem((GYM_QTSL_V0_REV,2))
//SORT GYM_QTSL_V0_REV 2 PathF
//SORT GYM_QTSL_V0_REV 0 Poly
//SORT GYM_QTSL_V0_REV 28 Port
//SORT GYM_QTSL_V0_REV 38 PortEq
//SORT GYM_QTSL_V0_REV 29 PortList
//SORT GYM_QTSL_V0_REV 36 PortPath
//SORT GYM_QTSLCERT_V0_REV 76 QDeadlineTable
//FUN GYM_QTSLCERT_V0_REV 342 QDeadlineTable/proof rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_QTSLCERT_V0_REV,76))) codomain=SortKey::Elem((GYM_QTSLCERT_V0_REV,1))
//FUN GYM_QTSLCERT_V0_REV 343 QDeadlineTable/table rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_QTSLCERT_V0_REV,76))) codomain=SortKey::Elem((GYM_QTSLCERT_V0_REV,13))
//SORT GYM_QTSLCERT_V0_REV 0 QJudgment
//SORT GYM_QTSLCERT_V0_REV 1 QProof
//FUN GYM_QTSLCERT_V0_REV 91 QProof/concludes rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_QTSLCERT_V0_REV,1))) codomain=SortKey::Elem((GYM_QTSLCERT_V0_REV,0))
//SORT GYM_QTSLCERT_V0_REV 13 QRatList
//SORT GYM_QTSLCERT_V0_REV 2 QSat
//FUN GYM_QTSLCERT_V0_REV 92 QSat/judgment rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_QTSLCERT_V0_REV,2))) codomain=SortKey::Elem((GYM_QTSLCERT_V0_REV,0))
//FUN GYM_QTSLCERT_V0_REV 312 QSat/spec rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_QTSLCERT_V0_REV,2))) codomain=SortKey::Elem((GYM_QTSL_V0_REV,20))
//FUN GYM_QTSLCERT_V0_REV 311 QSat/sys rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_QTSLCERT_V0_REV,2))) codomain=SortKey::Elem((GYM_QTSL_V0_REV,39))
//FUN GYM_QTSL_V0_REV 69 SAnd rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV,4))) codomain=SortKey::Elem((GYM_QTSL_V0_REV,1))
//FUN GYM_QTSL_V0_REV 68 SAtomGE rel=false side=false domain=DomainSig::Record(vec![("c".to_string(),SortKey::Ground(Ground::Q)),("poly".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,0)))]) codomain=SortKey::Elem((GYM_QTSL_V0_REV,1))
//FUN GYM_QTSL_V0_REV 67 SAtomLE rel=false side=false domain=DomainSig::Record(vec![("c".to_string(),SortKey::Ground(Ground::Q)),("poly".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,0)))]) codomain=SortKey::Elem((GYM_QTSL_V0_REV,1))
//FUN GYM_QTSL_V0_REV 66 SFalse rel=false side=false domain=DomainSig::Nullary codomain=SortKey::Elem((GYM_QTSL_V0_REV,1))
//FUN GYM_QTSL_V0_REV 71 SNot rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV,1))) codomain=SortKey::Elem((GYM_QTSL_V0_REV,1))
//FUN GYM_QTSL_V0_REV 70 SOr rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV,4))) codomain=SortKey::Elem((GYM_QTSL_V0_REV,1))
//FUN GYM_QTSL_V0_REV 72 SProbGE rel=false side=false domain=DomainSig::Record(vec![("p".to_string(),SortKey::Ground(Ground::Q)),("path".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,2)))]) codomain=SortKey::Elem((GYM_QTSL_V0_REV,1))
//FUN GYM_QTSL_V0_REV 206 SProbLE rel=false side=false domain=DomainSig::Record(vec![("path".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,2))),("q".to_string(),SortKey::Ground(Ground::Q))]) codomain=SortKey::Elem((GYM_QTSL_V0_REV,1))
//FUN GYM_QTSL_V0_REV 65 STrue rel=false side=false domain=DomainSig::Nullary codomain=SortKey::Elem((GYM_QTSL_V0_REV,1))
//SORT GYM_QTSL_V0_REV 20 Spec
//FUN GYM_QTSL_V0_REV 152 Spec/iface rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV,20))) codomain=SortKey::Elem((GYM_QTSL_V0_REV,30))
//FUN GYM_QTSL_V0_REV 142 Spec/name rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV,20))) codomain=SortKey::Ground(Ground::Str)
//FUN GYM_QTSL_V0_REV 143 Spec/root rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV,20))) codomain=SortKey::Elem((GYM_QTSL_V0_REV,1))
//SORT GYM_QTSL_V0_REV 1 StateF
//SORT GYM_QTSL_V0_REV 4 StateFList
//FUN GYM_QTSL_V0_REV 165 SysMech rel=false side=false domain=DomainSig::Record(vec![("mech".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,33)))]) codomain=SortKey::Elem((GYM_QTSL_V0_REV,39))
//FUN GYM_QTSL_V0_REV 166 SysWire rel=false side=false domain=DomainSig::Record(vec![("inner".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,40))),("wiring".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,37)))]) codomain=SortKey::Elem((GYM_QTSL_V0_REV,39))
//SORT GYM_QTSL_V0_REV 39 System
//FUN GYM_QTSL_V0_REV 169 System/iface rel=false side=false domain=DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV,39))) codomain=SortKey::Elem((GYM_QTSL_V0_REV,30))
//SORT GYM_QTSL_V0_REV 40 SystemList
//SORT GYM_QTSL_V0_REV 37 Wiring
//FUN GYM_QTSL_V0_REV 150 ilCons rel=false side=false domain=DomainSig::Record(vec![("head".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,30))),("tail".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,31)))]) codomain=SortKey::Elem((GYM_QTSL_V0_REV,31))
//FUN GYM_QTSL_V0_REV 149 ilNil rel=false side=false domain=DomainSig::Nullary codomain=SortKey::Elem((GYM_QTSL_V0_REV,31))
//FUN GYM_DTMC_V0_REV 14 kinit rel=false side=false domain=DomainSig::Record(vec![("dtmc".to_string(),SortKey::Elem((GYM_DTMC_V0_REV,0))),("state".to_string(),SortKey::Elem((GYM_DTMC_V0_REV,1)))]) codomain=SortKey::Ground(Ground::Q)
//FUN GYM_DTMC_V0_REV 13 kprob rel=false side=false domain=DomainSig::Record(vec![("act".to_string(),SortKey::Elem((GYM_DTMC_V0_REV,2))),("dst".to_string(),SortKey::Elem((GYM_DTMC_V0_REV,1))),("rew".to_string(),SortKey::Ground(Ground::Q)),("src".to_string(),SortKey::Elem((GYM_DTMC_V0_REV,1)))]) codomain=SortKey::Ground(Ground::Q)
//FUN GYM_QTSL_V0_REV 148 mkIface rel=false side=false domain=DomainSig::Record(vec![("invars".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,29))),("outvars".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,29)))]) codomain=SortKey::Elem((GYM_QTSL_V0_REV,30))
//FUN GYM_QTSL_V0_REV 145 mkPort rel=false side=false domain=DomainSig::Record(vec![("name".to_string(),SortKey::Ground(Ground::Str)),("shape".to_string(),SortKey::Ground(Ground::Shape))]) codomain=SortKey::Elem((GYM_QTSL_V0_REV,28))
//FUN GYM_QTSL_V0_REV 164 mkPortEq rel=false side=false domain=DomainSig::Record(vec![("a".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,36))),("b".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,36))),("wiring".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,37)))]) codomain=SortKey::Elem((GYM_QTSL_V0_REV,38))
//FUN GYM_QTSL_V0_REV 163 mkWiring rel=false side=false domain=DomainSig::Record(vec![("inner".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,31))),("outer".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,30)))]) codomain=SortKey::Elem((GYM_QTSL_V0_REV,37))
//FUN GYM_QTSL_V0_REV 63 pTerm rel=false side=false domain=DomainSig::Record(vec![("coeff".to_string(),SortKey::Ground(Ground::Q)),("expts".to_string(),SortKey::Ground(Ground::Shape)),("tail".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,0)))]) codomain=SortKey::Elem((GYM_QTSL_V0_REV,0))
//FUN GYM_QTSL_V0_REV 62 pZero rel=false side=false domain=DomainSig::Nullary codomain=SortKey::Elem((GYM_QTSL_V0_REV,0))
//FUN GYM_DTMC_V0_REV 19 pact rel=false side=false domain=DomainSig::Record(vec![("pol".to_string(),SortKey::Elem((GYM_DTMC_V0_REV,3))),("src".to_string(),SortKey::Elem((GYM_DTMC_V0_REV,1))),("t".to_string(),SortKey::Ground(Ground::Nat))]) codomain=SortKey::Elem((GYM_DTMC_V0_REV,2))
//FUN GYM_QTSL_V0_REV 161 ppInner rel=false side=false domain=DomainSig::Record(vec![("port".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,28))),("pos".to_string(),SortKey::Ground(Ground::Nat))]) codomain=SortKey::Elem((GYM_QTSL_V0_REV,36))
//FUN GYM_QTSL_V0_REV 147 ptCons rel=false side=false domain=DomainSig::Record(vec![("head".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,28))),("tail".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,29)))]) codomain=SortKey::Elem((GYM_QTSL_V0_REV,29))
//FUN GYM_QTSL_V0_REV 146 ptNil rel=false side=false domain=DomainSig::Nullary codomain=SortKey::Elem((GYM_QTSL_V0_REV,29))
//FUN GYM_QTSLCERT_V0_REV 111 qrlCons rel=false side=false domain=DomainSig::Record(vec![("head".to_string(),SortKey::Ground(Ground::Q)),("tail".to_string(),SortKey::Elem((GYM_QTSLCERT_V0_REV,13)))]) codomain=SortKey::Elem((GYM_QTSLCERT_V0_REV,13))
//FUN GYM_QTSLCERT_V0_REV 110 qrlNil rel=false side=false domain=DomainSig::Nullary codomain=SortKey::Elem((GYM_QTSLCERT_V0_REV,13))
//FUN GYM_QTSLCERT_V0_REV 344 qtsl_deadline_table rel=true side=true domain=DomainSig::Record(vec![("node".to_string(),SortKey::Elem((GYM_QTSLCERT_V0_REV,76)))]) codomain=-
//FUN GYM_QTSL_V0_REV 74 slCons rel=false side=false domain=DomainSig::Record(vec![("head".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,1))),("tail".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,4)))]) codomain=SortKey::Elem((GYM_QTSL_V0_REV,4))
//FUN GYM_QTSL_V0_REV 73 slNil rel=false side=false domain=DomainSig::Nullary codomain=SortKey::Elem((GYM_QTSL_V0_REV,4))
//FUN GYM_QTSL_V0_REV 168 syCons rel=false side=false domain=DomainSig::Record(vec![("head".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,39))),("tail".to_string(),SortKey::Elem((GYM_QTSL_V0_REV,40)))]) codomain=SortKey::Elem((GYM_QTSL_V0_REV,40))
//FUN GYM_QTSL_V0_REV 167 syNil rel=false side=false domain=DomainSig::Nullary codomain=SortKey::Elem((GYM_QTSL_V0_REV,40))

pub fn gym_v0_indexes() -> (TheoryIndex, TheoryIndex, TheoryIndex) {
    let mut q = TheoryIndex::new(GYM_QTSL_V0_REV);
    let mut qc = TheoryIndex::new(GYM_QTSLCERT_V0_REV);
    let mut dt = TheoryIndex::new(GYM_DTMC_V0_REV);
    dt.insert_sort("DAct", 2);
    dt.insert_fun(FunDecl {
        name: "DAct/dtmc".to_string(),
        chid: (GYM_DTMC_V0_REV, 10),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV, 2))),
        codomain: Some(SortKey::Elem((GYM_DTMC_V0_REV, 0))),
    });
    dt.insert_fun(FunDecl {
        name: "DAct/idx".to_string(),
        chid: (GYM_DTMC_V0_REV, 11),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV, 2))),
        codomain: Some(SortKey::Ground(Ground::Nat)),
    });
    dt.insert_fun(FunDecl {
        name: "DAct/name".to_string(),
        chid: (GYM_DTMC_V0_REV, 12),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV, 2))),
        codomain: Some(SortKey::Ground(Ground::Str)),
    });
    dt.insert_sort("DPolicy", 3);
    dt.insert_fun(FunDecl {
        name: "DPolicy/dtmc".to_string(),
        chid: (GYM_DTMC_V0_REV, 17),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV, 3))),
        codomain: Some(SortKey::Elem((GYM_DTMC_V0_REV, 0))),
    });
    dt.insert_fun(FunDecl {
        name: "DPolicy/horizon".to_string(),
        chid: (GYM_DTMC_V0_REV, 18),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV, 3))),
        codomain: Some(SortKey::Ground(Ground::Nat)),
    });
    dt.insert_fun(FunDecl {
        name: "DPolicy/name".to_string(),
        chid: (GYM_DTMC_V0_REV, 16),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV, 3))),
        codomain: Some(SortKey::Ground(Ground::Str)),
    });
    dt.insert_sort("DState", 1);
    dt.insert_fun(FunDecl {
        name: "DState/absorbing".to_string(),
        chid: (GYM_DTMC_V0_REV, 9),
        relational: true,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV, 1))),
        codomain: None,
    });
    dt.insert_fun(FunDecl {
        name: "DState/dtmc".to_string(),
        chid: (GYM_DTMC_V0_REV, 7),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV, 1))),
        codomain: Some(SortKey::Elem((GYM_DTMC_V0_REV, 0))),
    });
    dt.insert_fun(FunDecl {
        name: "DState/idx".to_string(),
        chid: (GYM_DTMC_V0_REV, 8),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV, 1))),
        codomain: Some(SortKey::Ground(Ground::Nat)),
    });
    dt.insert_sort("Dtmc", 0);
    dt.insert_fun(FunDecl {
        name: "Dtmc/name".to_string(),
        chid: (GYM_DTMC_V0_REV, 6),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_DTMC_V0_REV, 0))),
        codomain: Some(SortKey::Ground(Ground::Str)),
    });
    q.insert_sort("Iface", 30);
    q.insert_sort("IfaceList", 31);
    q.insert_sort("Mech", 33);
    dt.insert_fun(FunDecl {
        name: "Mech/dpolicy".to_string(),
        chid: (GYM_DTMC_V0_REV, 20),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV, 33))),
        codomain: Some(SortKey::Elem((GYM_DTMC_V0_REV, 3))),
    });
    dt.insert_fun(FunDecl {
        name: "Mech/dtmc".to_string(),
        chid: (GYM_DTMC_V0_REV, 15),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV, 33))),
        codomain: Some(SortKey::Elem((GYM_DTMC_V0_REV, 0))),
    });
    q.insert_fun(FunDecl {
        name: "Mech/iface".to_string(),
        chid: (GYM_QTSL_V0_REV, 156),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV, 33))),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 30))),
    });
    q.insert_fun(FunDecl {
        name: "Mech/name".to_string(),
        chid: (GYM_QTSL_V0_REV, 155),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV, 33))),
        codomain: Some(SortKey::Ground(Ground::Str)),
    });
    q.insert_fun(FunDecl {
        name: "PDeadline".to_string(),
        chid: (GYM_QTSL_V0_REV, 76),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("T".to_string(), SortKey::Ground(Ground::Q)),
            ("arg".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 1))),
            ("producerT".to_string(), SortKey::Ground(Ground::B)),
        ]),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 2))),
    });
    q.insert_sort("PathF", 2);
    q.insert_sort("Poly", 0);
    q.insert_sort("Port", 28);
    q.insert_sort("PortEq", 38);
    q.insert_sort("PortList", 29);
    q.insert_sort("PortPath", 36);
    qc.insert_sort("QDeadlineTable", 76);
    qc.insert_fun(FunDecl {
        name: "QDeadlineTable/proof".to_string(),
        chid: (GYM_QTSLCERT_V0_REV, 342),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_QTSLCERT_V0_REV, 76))),
        codomain: Some(SortKey::Elem((GYM_QTSLCERT_V0_REV, 1))),
    });
    qc.insert_fun(FunDecl {
        name: "QDeadlineTable/table".to_string(),
        chid: (GYM_QTSLCERT_V0_REV, 343),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_QTSLCERT_V0_REV, 76))),
        codomain: Some(SortKey::Elem((GYM_QTSLCERT_V0_REV, 13))),
    });
    qc.insert_sort("QJudgment", 0);
    qc.insert_sort("QProof", 1);
    qc.insert_fun(FunDecl {
        name: "QProof/concludes".to_string(),
        chid: (GYM_QTSLCERT_V0_REV, 91),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_QTSLCERT_V0_REV, 1))),
        codomain: Some(SortKey::Elem((GYM_QTSLCERT_V0_REV, 0))),
    });
    qc.insert_sort("QRatList", 13);
    qc.insert_sort("QSat", 2);
    qc.insert_fun(FunDecl {
        name: "QSat/judgment".to_string(),
        chid: (GYM_QTSLCERT_V0_REV, 92),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_QTSLCERT_V0_REV, 2))),
        codomain: Some(SortKey::Elem((GYM_QTSLCERT_V0_REV, 0))),
    });
    qc.insert_fun(FunDecl {
        name: "QSat/spec".to_string(),
        chid: (GYM_QTSLCERT_V0_REV, 312),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_QTSLCERT_V0_REV, 2))),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 20))),
    });
    qc.insert_fun(FunDecl {
        name: "QSat/sys".to_string(),
        chid: (GYM_QTSLCERT_V0_REV, 311),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_QTSLCERT_V0_REV, 2))),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 39))),
    });
    q.insert_fun(FunDecl {
        name: "SAnd".to_string(),
        chid: (GYM_QTSL_V0_REV, 69),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV, 4))),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 1))),
    });
    q.insert_fun(FunDecl {
        name: "SAtomGE".to_string(),
        chid: (GYM_QTSL_V0_REV, 68),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("c".to_string(), SortKey::Ground(Ground::Q)),
            ("poly".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 0))),
        ]),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 1))),
    });
    q.insert_fun(FunDecl {
        name: "SAtomLE".to_string(),
        chid: (GYM_QTSL_V0_REV, 67),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("c".to_string(), SortKey::Ground(Ground::Q)),
            ("poly".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 0))),
        ]),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 1))),
    });
    q.insert_fun(FunDecl {
        name: "SFalse".to_string(),
        chid: (GYM_QTSL_V0_REV, 66),
        relational: false,
        side_condition: false,
        domain: DomainSig::Nullary,
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 1))),
    });
    q.insert_fun(FunDecl {
        name: "SNot".to_string(),
        chid: (GYM_QTSL_V0_REV, 71),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV, 1))),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 1))),
    });
    q.insert_fun(FunDecl {
        name: "SOr".to_string(),
        chid: (GYM_QTSL_V0_REV, 70),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV, 4))),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 1))),
    });
    q.insert_fun(FunDecl {
        name: "SProbGE".to_string(),
        chid: (GYM_QTSL_V0_REV, 72),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("p".to_string(), SortKey::Ground(Ground::Q)),
            ("path".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 2))),
        ]),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 1))),
    });
    q.insert_fun(FunDecl {
        name: "SProbLE".to_string(),
        chid: (GYM_QTSL_V0_REV, 206),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("path".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 2))),
            ("q".to_string(), SortKey::Ground(Ground::Q)),
        ]),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 1))),
    });
    q.insert_fun(FunDecl {
        name: "STrue".to_string(),
        chid: (GYM_QTSL_V0_REV, 65),
        relational: false,
        side_condition: false,
        domain: DomainSig::Nullary,
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 1))),
    });
    q.insert_sort("Spec", 20);
    q.insert_fun(FunDecl {
        name: "Spec/iface".to_string(),
        chid: (GYM_QTSL_V0_REV, 152),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV, 20))),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 30))),
    });
    q.insert_fun(FunDecl {
        name: "Spec/name".to_string(),
        chid: (GYM_QTSL_V0_REV, 142),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV, 20))),
        codomain: Some(SortKey::Ground(Ground::Str)),
    });
    q.insert_fun(FunDecl {
        name: "Spec/root".to_string(),
        chid: (GYM_QTSL_V0_REV, 143),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV, 20))),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 1))),
    });
    q.insert_sort("StateF", 1);
    q.insert_sort("StateFList", 4);
    q.insert_fun(FunDecl {
        name: "SysMech".to_string(),
        chid: (GYM_QTSL_V0_REV, 165),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![(
            "mech".to_string(),
            SortKey::Elem((GYM_QTSL_V0_REV, 33)),
        )]),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 39))),
    });
    q.insert_fun(FunDecl {
        name: "SysWire".to_string(),
        chid: (GYM_QTSL_V0_REV, 166),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("inner".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 40))),
            ("wiring".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 37))),
        ]),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 39))),
    });
    q.insert_sort("System", 39);
    q.insert_fun(FunDecl {
        name: "System/iface".to_string(),
        chid: (GYM_QTSL_V0_REV, 169),
        relational: false,
        side_condition: false,
        domain: DomainSig::Unary(SortKey::Elem((GYM_QTSL_V0_REV, 39))),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 30))),
    });
    q.insert_sort("SystemList", 40);
    q.insert_sort("Wiring", 37);
    q.insert_fun(FunDecl {
        name: "ilCons".to_string(),
        chid: (GYM_QTSL_V0_REV, 150),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("head".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 30))),
            ("tail".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 31))),
        ]),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 31))),
    });
    q.insert_fun(FunDecl {
        name: "ilNil".to_string(),
        chid: (GYM_QTSL_V0_REV, 149),
        relational: false,
        side_condition: false,
        domain: DomainSig::Nullary,
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 31))),
    });
    dt.insert_fun(FunDecl {
        name: "kinit".to_string(),
        chid: (GYM_DTMC_V0_REV, 14),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("dtmc".to_string(), SortKey::Elem((GYM_DTMC_V0_REV, 0))),
            ("state".to_string(), SortKey::Elem((GYM_DTMC_V0_REV, 1))),
        ]),
        codomain: Some(SortKey::Ground(Ground::Q)),
    });
    dt.insert_fun(FunDecl {
        name: "kprob".to_string(),
        chid: (GYM_DTMC_V0_REV, 13),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("act".to_string(), SortKey::Elem((GYM_DTMC_V0_REV, 2))),
            ("dst".to_string(), SortKey::Elem((GYM_DTMC_V0_REV, 1))),
            ("rew".to_string(), SortKey::Ground(Ground::Q)),
            ("src".to_string(), SortKey::Elem((GYM_DTMC_V0_REV, 1))),
        ]),
        codomain: Some(SortKey::Ground(Ground::Q)),
    });
    q.insert_fun(FunDecl {
        name: "mkIface".to_string(),
        chid: (GYM_QTSL_V0_REV, 148),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("invars".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 29))),
            ("outvars".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 29))),
        ]),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 30))),
    });
    q.insert_fun(FunDecl {
        name: "mkPort".to_string(),
        chid: (GYM_QTSL_V0_REV, 145),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("name".to_string(), SortKey::Ground(Ground::Str)),
            ("shape".to_string(), SortKey::Ground(Ground::Shape)),
        ]),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 28))),
    });
    q.insert_fun(FunDecl {
        name: "mkPortEq".to_string(),
        chid: (GYM_QTSL_V0_REV, 164),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("a".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 36))),
            ("b".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 36))),
            ("wiring".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 37))),
        ]),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 38))),
    });
    q.insert_fun(FunDecl {
        name: "mkWiring".to_string(),
        chid: (GYM_QTSL_V0_REV, 163),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("inner".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 31))),
            ("outer".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 30))),
        ]),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 37))),
    });
    q.insert_fun(FunDecl {
        name: "pTerm".to_string(),
        chid: (GYM_QTSL_V0_REV, 63),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("coeff".to_string(), SortKey::Ground(Ground::Q)),
            ("expts".to_string(), SortKey::Ground(Ground::Shape)),
            ("tail".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 0))),
        ]),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 0))),
    });
    q.insert_fun(FunDecl {
        name: "pZero".to_string(),
        chid: (GYM_QTSL_V0_REV, 62),
        relational: false,
        side_condition: false,
        domain: DomainSig::Nullary,
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 0))),
    });
    dt.insert_fun(FunDecl {
        name: "pact".to_string(),
        chid: (GYM_DTMC_V0_REV, 19),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("pol".to_string(), SortKey::Elem((GYM_DTMC_V0_REV, 3))),
            ("src".to_string(), SortKey::Elem((GYM_DTMC_V0_REV, 1))),
            ("t".to_string(), SortKey::Ground(Ground::Nat)),
        ]),
        codomain: Some(SortKey::Elem((GYM_DTMC_V0_REV, 2))),
    });
    q.insert_fun(FunDecl {
        name: "ppInner".to_string(),
        chid: (GYM_QTSL_V0_REV, 161),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("port".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 28))),
            ("pos".to_string(), SortKey::Ground(Ground::Nat)),
        ]),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 36))),
    });
    q.insert_fun(FunDecl {
        name: "ptCons".to_string(),
        chid: (GYM_QTSL_V0_REV, 147),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("head".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 28))),
            ("tail".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 29))),
        ]),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 29))),
    });
    q.insert_fun(FunDecl {
        name: "ptNil".to_string(),
        chid: (GYM_QTSL_V0_REV, 146),
        relational: false,
        side_condition: false,
        domain: DomainSig::Nullary,
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 29))),
    });
    qc.insert_fun(FunDecl {
        name: "qrlCons".to_string(),
        chid: (GYM_QTSLCERT_V0_REV, 111),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("head".to_string(), SortKey::Ground(Ground::Q)),
            ("tail".to_string(), SortKey::Elem((GYM_QTSLCERT_V0_REV, 13))),
        ]),
        codomain: Some(SortKey::Elem((GYM_QTSLCERT_V0_REV, 13))),
    });
    qc.insert_fun(FunDecl {
        name: "qrlNil".to_string(),
        chid: (GYM_QTSLCERT_V0_REV, 110),
        relational: false,
        side_condition: false,
        domain: DomainSig::Nullary,
        codomain: Some(SortKey::Elem((GYM_QTSLCERT_V0_REV, 13))),
    });
    qc.insert_fun(FunDecl {
        name: "qtsl_deadline_table".to_string(),
        chid: (GYM_QTSLCERT_V0_REV, 344),
        relational: true,
        side_condition: true,
        domain: DomainSig::Record(vec![(
            "node".to_string(),
            SortKey::Elem((GYM_QTSLCERT_V0_REV, 76)),
        )]),
        codomain: None,
    });
    q.insert_fun(FunDecl {
        name: "slCons".to_string(),
        chid: (GYM_QTSL_V0_REV, 74),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("head".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 1))),
            ("tail".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 4))),
        ]),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 4))),
    });
    q.insert_fun(FunDecl {
        name: "slNil".to_string(),
        chid: (GYM_QTSL_V0_REV, 73),
        relational: false,
        side_condition: false,
        domain: DomainSig::Nullary,
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 4))),
    });
    q.insert_fun(FunDecl {
        name: "syCons".to_string(),
        chid: (GYM_QTSL_V0_REV, 168),
        relational: false,
        side_condition: false,
        domain: DomainSig::Record(vec![
            ("head".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 39))),
            ("tail".to_string(), SortKey::Elem((GYM_QTSL_V0_REV, 40))),
        ]),
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 40))),
    });
    q.insert_fun(FunDecl {
        name: "syNil".to_string(),
        chid: (GYM_QTSL_V0_REV, 167),
        relational: false,
        side_condition: false,
        domain: DomainSig::Nullary,
        codomain: Some(SortKey::Elem((GYM_QTSL_V0_REV, 40))),
    });
    (q, qc, dt)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{QtslGroundProvider, QtslVocab};

    #[test]
    fn construction_is_deterministic() {
        let (a1, b1, c1) = gym_v0_indexes();
        let (a2, b2, c2) = gym_v0_indexes();
        for (x, y) in [(&a1, &a2), (&b1, &b2), (&c1, &c2)] {
            assert_eq!(x.funs.len(), y.funs.len());
            for (f, g) in x.funs.iter().zip(y.funs.iter()) {
                assert_eq!(f.name, g.name);
                assert_eq!(f.chid, g.chid);
                assert_eq!(f.domain, g.domain);
                assert_eq!(f.codomain, g.codomain);
            }
        }
    }

    #[test]
    fn deadline_family_resolves_and_claim_binds() {
        let (q, qc, dt) = gym_v0_indexes();
        let vocab = QtslVocab::build(&[&q, &qc, &dt]);
        assert!(
            vocab.deadline.is_some(),
            "deadline family must resolve on the gym slice; notes: {:?}",
            vocab.notes
        );
        let provider = QtslGroundProvider::new(vec![[0x2F; 32]], vocab);
        for name in GYM_V0_OBLIGATIONS {
            assert!(provider.local_by_name(name).is_some(), "`{name}` must bind");
        }
    }

    /// The cross-repo pins fixture: every slice entry's (kind, dep
    /// index, counter, name) matches the committed table the producer
    /// side also carries byte-identically.
    #[test]
    fn pinned_counters_match_the_shared_fixture() {
        let text = include_str!("../../tests/fixtures/gym_v0_pins.txt");
        let (q, qc, dt) = gym_v0_indexes();
        let slices = [&q, &qc, &dt];
        let mut n = 0usize;
        for line in text.lines().filter(|l| !l.starts_with('#')) {
            let mut it = line.split_whitespace();
            let kind = it.next().expect("kind");
            let dep: usize = it.next().expect("dep").parse().expect("dep index");
            let ctr: u32 = it.next().expect("counter").parse().expect("counter");
            let name = it.next().expect("name");
            let ix = slices[dep];
            match kind {
                "sort" => {
                    let chid = ix.sort(name).unwrap_or_else(|| panic!("sort `{name}`"));
                    assert_eq!(chid, (ix.commit, ctr), "sort `{name}` counter");
                }
                "fun" => {
                    let decl = ix.fun(name).unwrap_or_else(|| panic!("fun `{name}`"));
                    assert_eq!(decl.chid, (ix.commit, ctr), "fun `{name}` counter");
                }
                other => panic!("unknown pin kind `{other}`"),
            }
            n += 1;
        }
        // The fixture covers the whole slice: entry counts agree.
        let total: usize = slices
            .iter()
            .map(|ix| ix.funs.len() + ix.sorts_by_name.len())
            .sum();
        assert_eq!(n, total, "fixture rows == slice declarations");
    }
}
