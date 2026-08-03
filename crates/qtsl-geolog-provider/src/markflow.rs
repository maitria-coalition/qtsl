//! `qtsl_wire_markflow`: the MarkFlow walk — the ∃-dual of the
//! causality walk, demanded on every `QWireComposeMarks` node (the
//! liveness sibling of `QWireCompose`, event 5).
//!
//! Semantic authority: the Qtsl theory's marks-node block (the
//! declaration comment above `qtsl_wire_markflow`: two columns — stage
//! feasibility + carve coverage — bounded recompute over the node's
//! declaration closure, never chase derivation), the W-CYCLIC-AG design
//! memo r5 §8.2/§8.2a/§8.6, and the Lean specs `MarkFlowFeasible`
//! (AGComposeMarks) / `CarveClosure` (AGComposeCarves), consumed
//! abstractly per the event-5 mint's M-3 — the diagonal species are
//! its dischargers.
//!
//! # The walk, two columns
//!
//! **Stage column** — the producer supplies one rational stage label
//! per demanded mark (`QWireComposeMarks/schedule`, positional against
//! the components: mark `i` is component `i`'s guarantee, the Lean
//! `t : Fin n`). The walk verifies the difference-constraint system at
//! the labels: label equality across instantaneous wires (`t[i] =
//! t[j]` per directed wire `j→i`), label nonnegativity (lag `0 ≤
//! t[i]` — no delivery precedes its pipe's fill), each violated
//! constraint a decided-false with the row named. Feasibility ADMITS
//! consistent cycles (the all-ones loop) and refuses time-travel; no
//! well-foundedness anywhere.
//!
//! **Carve column** — the exact-lag rows force every admitted
//! dependency cycle to total lag zero and one shared label, so the
//! zero-lag cycle roster is an SCC pass on the instant subgraph
//! (nontrivial = size > 1 or a self-loop, canonically ordered by
//! minimal member position). Per nontrivial cycle: every member's
//! mark carries a carve (a `qcvCons {wire, gate}` entry whose wire
//! rides a class the member delivers into the cycle), the carve_rows
//! pairing arithmetic holds (2 rows per carve — containment then
//! carved-delivery, in carve-list order: list-shape obligations live
//! in this walk, the mint's M-4), and one species-tagged diagonal
//! certificate per cycle (`QDiagCert`, kind in the closed five-genus
//! `dgPoint`/`dgEnum`/`dgContract`/`dgConvex`/`dgMonotone`).
//! Producers MAY carve all marks; off-cycle carves are TOLERATED
//! (M-2) and shape-checked only — the chaining theorems make them
//! redundant warrant, so their content is not demanded.
//!
//! # The v1 decided fragment (the walk-adjudication pass, A-1…A-9 in
//! # the inc-3 findings file)
//!
//! The event-5 mint pinned the SPINES (M-1…M-6) and deliberately left
//! three row-content conventions unminted: the latency-row lag
//! encoding ("the general difference-constraint form is the mint's to
//! pin" — never pinned), the diagonal species' row conventions, and
//! the containment/carved-delivery citation forms. v1 therefore:
//!
//! - **decides** the fragment the landed vocabulary determines:
//!   components classified INSTANT (lag 0) iff `SysMech` ∧
//!   `Manifest/varnames` empty ∧ no attached `sys_transition` rows —
//!   the syswire-banked stateless reading ("a copy delivers at lag
//!   0"). On that fragment every wire is instantaneous, the whole
//!   graph is the instant subgraph, and the stage/coverage/pairing
//!   arithmetic is decided exactly;
//! - **refuses, named**, every component whose delivery lag is not
//!   row-decidable (stateful/Moore, transition-bearing, nested
//!   `SysWire`, `SysHole`) — deriving a lag from clock wings or
//!   guessing it from latency-row Proof leaves would be premise-tier
//!   content this walk has no convention to read;
//! - **refuses, named**, cycle-bearing nodes whose STRUCTURE passes:
//!   deciding Holds while the Z5-discriminating diagonal content is
//!   unchecked would be unchecked admission. Holds is reachable at v1
//!   only for acyclic instant graphs — exactly the chaining-theorem
//!   case, where the theory itself demands no diagonal.
//!
//! Decided violations surface through the provider's named-violations
//! register (design memo F-4), exactly as the store-seam family's do.
//! This family needs NO store: carve gates are cited by digest and
//! their conformance is `qtsl_gate_scalar`'s own chased demand
//! (`ax/wf/qcarve_gate_scalar`), never re-checked here.

use crate::qq::QQ;
use crate::roster::{EntryRow, RelKind};
use crate::rowctx::{CertRows, CtorRow, RelRow};
use crate::theory::{Chid, DomainSig, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use std::collections::HashMap;

/// The markflow family's row of the claimed roster (appended LAST at
/// registration — provider.rs; every existing roster position is
/// unchanged).
pub(crate) const ENTRIES: &[EntryRow] = &[(
    "qtsl_wire_markflow",
    &[("node", "QWireComposeMarks")],
    RelKind::Markflow,
)];

/// Budgets: refusal beyond, never divergence.
pub const MARKFLOW_MAX_COMPONENTS: usize = 1 << 10;
pub const MARKFLOW_MAX_PORTS: usize = 1 << 12;
pub const MARKFLOW_MAX_PORTEQ: usize = 1 << 14;
pub const MARKFLOW_MAX_CARVES: usize = 1 << 12;
const MAX_DECODE_STEPS: usize = 1 << 20;

// ---------------------------------------------------------------------
// Vocabulary
// ---------------------------------------------------------------------

/// The marks-node vocabulary, pinned at resolution (names select,
/// shapes verify, identities pin). A production index deriving a
/// different shape fails resolution — the family is then not claimed
/// (safe-fail), never mis-decoded.
#[derive(Debug, Clone)]
pub struct MarkflowVocab {
    // the node's ten attributes
    a_proof: Chid,
    a_components: Chid,
    a_wirecert: Chid,
    a_latency: Chid,
    a_schedule: Chid,
    a_carves: Chid,
    a_carve_rows: Chid,
    a_diagonals: Chid,
    a_entailment: Chid,
    a_wellposed: Chid,
    // satisfaction citations
    qsat_sys: Chid,
    qsatlist_sort: Chid,
    qsat_nil: Chid,
    qsat_cons: Chid,
    // the cited certificate
    cert_wiring: Chid,
    cert_premises: Chid,
    qspeclist_sort: Chid,
    qspec_nil: Chid,
    qspec_cons: Chid,
    // wiring / ports
    wiring_sort: Chid,
    mk_wiring: Chid,
    mk_port_eq: Chid,
    portpath_sort: Chid,
    pp_inner: Chid,
    pp_outer: Chid,
    iface_sort: Chid,
    mk_iface: Chid,
    ifacelist_sort: Chid,
    il_nil: Chid,
    il_cons: Chid,
    portlist_sort: Chid,
    pt_nil: Chid,
    pt_cons: Chid,
    // component presentations (the v1 lag classification)
    system_sort: Chid,
    sys_mech: Chid,
    sys_wire: Chid,
    sys_hole: Chid,
    mech_manifest: Chid,
    manifest_varnames: Chid,
    strlist_sort: Chid,
    str_nil: Chid,
    str_cons: Chid,
    sys_transition: Chid,
    // the walk's list spines
    qratlist_sort: Chid,
    qrl_nil: Chid,
    qrl_cons: Chid,
    qprooflist_sort: Chid,
    qpl_nil: Chid,
    qpl_cons: Chid,
    qcarvelist_sort: Chid,
    qcv_nil: Chid,
    qcv_cons: Chid,
    qdiaglist_sort: Chid,
    qdg_nil: Chid,
    qdg_cons: Chid,
    // diagonal certificates
    diag_kind: Chid,
    diag_rows: Chid,
    diagkind_sort: Chid,
    dg_point: Chid,
    dg_enum: Chid,
    dg_contract: Chid,
    dg_convex: Chid,
    dg_monotone: Chid,
    /// Per-sort constructor rosters for the value-like sorts the walk
    /// `sole`-resolves on: sort chid → (fun chid → domain).
    ctors: HashMap<Chid, HashMap<Chid, DomainSig>>,
}

/// Build the marks-node vocabulary. `Err` → the family is not claimed
/// (C-ORACLE safe-fail; reason recorded on the provider's notes).
pub fn build_markflow_vocab(indices: &[&TheoryIndex]) -> Result<MarkflowVocab, String> {
    let sort = |name: &str| -> Result<Chid, String> {
        for index in indices {
            if let Some(c) = index.sort(name) {
                return Ok(c);
            }
        }
        Err(format!("no `{name}` sort among the swept revisions"))
    };
    // An attribute: unary on its subject, codomain verified by the
    // caller where it matters.
    let attr = |name: &str, subject: Chid| -> Result<(Chid, SortKey), String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational {
                return Err(format!("`{name}` is relational, expected an attribute"));
            }
            if d.domain != DomainSig::Unary(SortKey::Elem(subject)) {
                return Err(format!(
                    "`{name}`: expected a unary domain on its subject sort"
                ));
            }
            let Some(cod) = d.codomain else {
                return Err(format!("`{name}` has no codomain"));
            };
            return Ok((d.chid, cod));
        }
        Err(format!("no `{name}` attribute among the swept revisions"))
    };
    let ctor = |name: &str, want_cod: Chid| -> Result<(Chid, DomainSig), String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational || d.codomain != Some(SortKey::Elem(want_cod)) {
                return Err(format!(
                    "`{name}` is not a constructor of the expected sort"
                ));
            }
            return Ok((d.chid, d.domain.clone()));
        }
        Err(format!("no `{name}` constructor among the swept revisions"))
    };
    let rel = |name: &str, arity: usize| -> Result<Chid, String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            let ok = d.relational
                && d.codomain.is_none()
                && matches!(&d.domain, DomainSig::Record(fs) if fs.len() == arity);
            if !ok {
                return Err(format!(
                    "`{name}` does not have the expected relation shape"
                ));
            }
            return Ok(d.chid);
        }
        Err(format!("no `{name}` declaration among the swept revisions"))
    };

    let node_sort = sort("QWireComposeMarks")?;
    let qsatlist_sort = sort("QSatList")?;
    let qsat_sort = sort("QSat")?;
    let cert_sort = sort("QWireCert")?;
    let qspeclist_sort = sort("QSpecList")?;
    let wiring_sort = sort("Wiring")?;
    let portpath_sort = sort("PortPath")?;
    let iface_sort = sort("Iface")?;
    let ifacelist_sort = sort("IfaceList")?;
    let portlist_sort = sort("PortList")?;
    let system_sort = sort("System")?;
    let strlist_sort = sort("StrList")?;
    let qratlist_sort = sort("QRatList")?;
    let qprooflist_sort = sort("QProofList")?;
    let qcarvelist_sort = sort("QCarveList")?;
    let qdiaglist_sort = sort("QDiagList")?;
    let qdiagcert_sort = sort("QDiagCert")?;
    let diagkind_sort = sort("DiagKind")?;

    let need = |name: &str, got: &SortKey, want: Chid| -> Result<(), String> {
        if *got == SortKey::Elem(want) {
            Ok(())
        } else {
            Err(format!("`{name}`: codomain is not the expected sort"))
        }
    };

    let (a_proof, _) = attr("QWireComposeMarks/proof", node_sort)?;
    let (a_components, c) = attr("QWireComposeMarks/components", node_sort)?;
    need("QWireComposeMarks/components", &c, qsatlist_sort)?;
    let (a_wirecert, c) = attr("QWireComposeMarks/wirecert", node_sort)?;
    need("QWireComposeMarks/wirecert", &c, cert_sort)?;
    let (a_latency, c) = attr("QWireComposeMarks/latency_rows", node_sort)?;
    need("QWireComposeMarks/latency_rows", &c, qprooflist_sort)?;
    let (a_schedule, c) = attr("QWireComposeMarks/schedule", node_sort)?;
    need("QWireComposeMarks/schedule", &c, qratlist_sort)?;
    let (a_carves, c) = attr("QWireComposeMarks/carves", node_sort)?;
    need("QWireComposeMarks/carves", &c, qcarvelist_sort)?;
    let (a_carve_rows, c) = attr("QWireComposeMarks/carve_rows", node_sort)?;
    need("QWireComposeMarks/carve_rows", &c, qprooflist_sort)?;
    let (a_diagonals, c) = attr("QWireComposeMarks/diagonal_rows", node_sort)?;
    need("QWireComposeMarks/diagonal_rows", &c, qdiaglist_sort)?;
    let (a_entailment, _) = attr("QWireComposeMarks/entailment", node_sort)?;
    let (a_wellposed, c) = attr("QWireComposeMarks/wellposedness", node_sort)?;
    need("QWireComposeMarks/wellposedness", &c, qprooflist_sort)?;

    let (qsat_sys, c) = attr("QSat/sys", qsat_sort)?;
    need("QSat/sys", &c, system_sort)?;
    let (cert_wiring, c) = attr("QWireCert/wiring", cert_sort)?;
    need("QWireCert/wiring", &c, wiring_sort)?;
    let (cert_premises, c) = attr("QWireCert/premises", cert_sort)?;
    need("QWireCert/premises", &c, qspeclist_sort)?;
    let (diag_kind, c) = attr("QDiagCert/kind", qdiagcert_sort)?;
    need("QDiagCert/kind", &c, diagkind_sort)?;
    let (diag_rows, c) = attr("QDiagCert/rows", qdiagcert_sort)?;
    need("QDiagCert/rows", &c, qprooflist_sort)?;

    let (manifest_varnames, c) = attr("Manifest/varnames", sort("Manifest")?)?;
    need("Manifest/varnames", &c, strlist_sort)?;

    let mut ctors: HashMap<Chid, HashMap<Chid, DomainSig>> = HashMap::new();
    let mut add = |sort: Chid, pair: (Chid, DomainSig)| -> Chid {
        ctors.entry(sort).or_default().insert(pair.0, pair.1);
        pair.0
    };

    let qsat_nil = add(qsatlist_sort, ctor("qsatNil", qsatlist_sort)?);
    let qsat_cons = add(qsatlist_sort, ctor("qsatCons", qsatlist_sort)?);
    let qspec_nil = add(qspeclist_sort, ctor("qspecNil", qspeclist_sort)?);
    let qspec_cons = add(qspeclist_sort, ctor("qspecCons", qspeclist_sort)?);
    let qrl_nil = add(qratlist_sort, ctor("qrlNil", qratlist_sort)?);
    let qrl_cons = add(qratlist_sort, ctor("qrlCons", qratlist_sort)?);
    let qpl_nil = add(qprooflist_sort, ctor("qplNil", qprooflist_sort)?);
    let qpl_cons = add(qprooflist_sort, ctor("qplCons", qprooflist_sort)?);
    let qcv_nil = add(qcarvelist_sort, ctor("qcvNil", qcarvelist_sort)?);
    let qcv_cons = add(qcarvelist_sort, ctor("qcvCons", qcarvelist_sort)?);
    let qdg_nil = add(qdiaglist_sort, ctor("qdgNil", qdiaglist_sort)?);
    let qdg_cons = add(qdiaglist_sort, ctor("qdgCons", qdiaglist_sort)?);
    let mk_wiring = add(wiring_sort, ctor("mkWiring", wiring_sort)?);
    let mk_port_eq = add(sort("PortEq")?, ctor("mkPortEq", sort("PortEq")?)?);
    let pp_inner = add(portpath_sort, ctor("ppInner", portpath_sort)?);
    let pp_outer = add(portpath_sort, ctor("ppOuter", portpath_sort)?);
    let mk_iface = add(iface_sort, ctor("mkIface", iface_sort)?);
    let il_nil = add(ifacelist_sort, ctor("ilNil", ifacelist_sort)?);
    let il_cons = add(ifacelist_sort, ctor("ilCons", ifacelist_sort)?);
    let pt_nil = add(portlist_sort, ctor("ptNil", portlist_sort)?);
    let pt_cons = add(portlist_sort, ctor("ptCons", portlist_sort)?);
    let sys_mech = add(system_sort, ctor("SysMech", system_sort)?);
    let sys_wire = add(system_sort, ctor("SysWire", system_sort)?);
    let sys_hole = add(system_sort, ctor("SysHole", system_sort)?);
    let str_nil = add(strlist_sort, ctor("strNil", strlist_sort)?);
    let str_cons = add(strlist_sort, ctor("strCons", strlist_sort)?);
    let dg_point = add(diagkind_sort, ctor("dgPoint", diagkind_sort)?);
    let dg_enum = add(diagkind_sort, ctor("dgEnum", diagkind_sort)?);
    let dg_contract = add(diagkind_sort, ctor("dgContract", diagkind_sort)?);
    let dg_convex = add(diagkind_sort, ctor("dgConvex", diagkind_sort)?);
    let dg_monotone = add(diagkind_sort, ctor("dgMonotone", diagkind_sort)?);

    let mech_manifest = rel("mech_manifest", 2)?;
    let sys_transition = rel("sys_transition", 2)?;

    Ok(MarkflowVocab {
        a_proof,
        a_components,
        a_wirecert,
        a_latency,
        a_schedule,
        a_carves,
        a_carve_rows,
        a_diagonals,
        a_entailment,
        a_wellposed,
        qsat_sys,
        qsatlist_sort,
        qsat_nil,
        qsat_cons,
        cert_wiring,
        cert_premises,
        qspeclist_sort,
        qspec_nil,
        qspec_cons,
        wiring_sort,
        mk_wiring,
        mk_port_eq,
        portpath_sort,
        pp_inner,
        pp_outer,
        iface_sort,
        mk_iface,
        ifacelist_sort,
        il_nil,
        il_cons,
        portlist_sort,
        pt_nil,
        pt_cons,
        system_sort,
        sys_mech,
        sys_wire,
        sys_hole,
        mech_manifest,
        manifest_varnames,
        strlist_sort,
        str_nil,
        str_cons,
        sys_transition,
        qratlist_sort,
        qrl_nil,
        qrl_cons,
        qprooflist_sort,
        qpl_nil,
        qpl_cons,
        qcarvelist_sort,
        qcv_nil,
        qcv_cons,
        qdiaglist_sort,
        qdg_nil,
        qdg_cons,
        diag_kind,
        diag_rows,
        diagkind_sort,
        dg_point,
        dg_enum,
        dg_contract,
        dg_convex,
        dg_monotone,
        ctors,
    })
}

// ---------------------------------------------------------------------
// The walk
// ---------------------------------------------------------------------

/// Three-valued walk outcome: `Ok(Ok(()))` holds, `Ok(Err(why))`
/// decided false (the dispatch banks the named violation),
/// `Err(reason)` refuses.
type Out = Result<Result<(), String>, String>;

/// Port-space node ids for one composite level (single level — the v1
/// fragment refuses nested composites at classification, so the walk
/// never recurses).
#[derive(Clone, Copy)]
enum PNode {
    Inner { pos: usize, out: bool, idx: usize },
    Outer { out: bool, idx: usize },
}

struct Level {
    /// per inner position: (in-port elems, out-port elems), from the
    /// wiring's DECLARED interfaces (positional agreement with the
    /// components' presented interfaces is WiringMatch's chase
    /// business; this walk only needs the declared port rosters to
    /// resolve PortPaths).
    inner_ports: Vec<(Vec<u32>, Vec<u32>)>,
    outer_ports: (Vec<u32>, Vec<u32>),
}

impl Level {
    fn base(&self, pos: usize) -> usize {
        let mut b = 0;
        for p in self.inner_ports.iter().take(pos) {
            b += p.0.len() + p.1.len();
        }
        b
    }
    fn node(&self, n: PNode) -> usize {
        match n {
            PNode::Inner { pos, out, idx } => {
                self.base(pos)
                    + if out {
                        self.inner_ports[pos].0.len()
                    } else {
                        0
                    }
                    + idx
            }
            PNode::Outer { out, idx } => {
                self.base(self.inner_ports.len())
                    + if out { self.outer_ports.0.len() } else { 0 }
                    + idx
            }
        }
    }
    fn n_nodes(&self) -> usize {
        self.base(self.inner_ports.len()) + self.outer_ports.0.len() + self.outer_ports.1.len()
    }
}

struct UnionFind {
    parent: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> UnionFind {
        UnionFind {
            parent: (0..n).collect(),
        }
    }
    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }
    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent[ra] = rb;
        }
    }
}

struct Decoder<'a> {
    v: &'a MarkflowVocab,
    rows: &'a CertRows,
    steps: usize,
}

const NAME: &str = "qtsl_wire_markflow";

impl<'a> Decoder<'a> {
    fn step(&mut self) -> Result<(), String> {
        self.steps += 1;
        if self.steps > MAX_DECODE_STEPS {
            Err(format!(
                "`{NAME}`: decode beyond the step budget ({MAX_DECODE_STEPS}) — refusing"
            ))
        } else {
            Ok(())
        }
    }

    fn elem(&self, val: &Value) -> Result<u32, String> {
        match val {
            Value::Ref(geolog_envelope::ElemRef::Local(e)) => Ok(*e),
            _ => Err(format!(
                "`{NAME}`: expected a local element ref, found a literal or external \
                 ref — cross-commit structure is not walkable here, refusing"
            )),
        }
    }

    fn q_lit(&self, val: &Value, what: &str) -> Result<QQ, String> {
        match val {
            Value::Lit(l) => QQ::from_q_literal(l).ok_or_else(|| {
                format!("`{NAME}`: {what} is not an exact-Q literal — malformed rows, refusing")
            }),
            _ => Err(format!("`{NAME}`: {what} is not a literal cell — refusing")),
        }
    }

    /// The sole producing row of `elem` among `sort`'s pinned
    /// constructor roster. Zero rows: the element is unresolvable in
    /// this body (entity or foreign) — refuse. Two: ambiguous.
    fn sole(&mut self, sort: Chid, elem: u32) -> Result<&'a CtorRow, String> {
        self.step()?;
        let Some(roster) = self.v.ctors.get(&sort) else {
            return Err(format!(
                "`{NAME}`: internal — no constructor roster for the requested sort"
            ));
        };
        let mut found: Option<&'a CtorRow> = None;
        for row in self.rows.producers(elem) {
            if !roster.contains_key(&row.fun) {
                continue;
            }
            if found.is_some() {
                return Err(format!(
                    "`{NAME}`: element {elem} is produced by two constructor rows — \
                     ambiguous (P-FUN territory), refusing"
                ));
            }
            found = Some(row);
        }
        found.ok_or_else(|| {
            format!(
                "`{NAME}`: element {elem} has no constructor row of the expected sort \
                 in this body — undecidable, refusing"
            )
        })
    }

    /// The sole attribute row `fun(subject) = v`, if any; two distinct
    /// rows refuse (functionality is admission conformance).
    fn sole_attr(
        &mut self,
        subject: u32,
        fun: Chid,
        what: &str,
    ) -> Result<Option<&'a Value>, String> {
        self.step()?;
        let mut found: Option<&'a Value> = None;
        for row in self.rows.attrs(subject) {
            if row.fun != fun || row.args.len() != 1 {
                continue;
            }
            if let Some(prev) = found {
                if *prev != row.value {
                    return Err(format!(
                        "`{NAME}`: `{what}` stated twice for element {subject} with \
                         distinct values — ambiguous, refusing"
                    ));
                }
                continue;
            }
            found = Some(&row.value);
        }
        Ok(found)
    }

    fn need_attr(&mut self, subject: u32, fun: Chid, what: &str) -> Result<&'a Value, String> {
        self.sole_attr(subject, fun, what)?.ok_or_else(|| {
            format!("`{NAME}`: node walk found no `{what}` row for element {subject} — refusing")
        })
    }

    /// Distinct relation rows with `elem` at argument `subject_index`.
    fn distinct_rel_rows(
        &mut self,
        rel: Chid,
        subject_index: usize,
        elem: u32,
        arity: usize,
        what: &str,
    ) -> Result<Vec<&'a RelRow>, String> {
        self.step()?;
        let mut out: Vec<&'a RelRow> = Vec::new();
        for row in self.rows.rel_rows_citing(elem) {
            if row.rel != rel || row.args.len() != arity {
                continue;
            }
            match &row.args[subject_index] {
                Value::Ref(geolog_envelope::ElemRef::Local(e)) if *e == elem => {}
                _ => continue,
            }
            if !out.iter().any(|r| r.args == row.args) {
                out.push(row);
            }
        }
        let _ = what;
        Ok(out)
    }

    /// Walk a nil/cons list, returning the cons rows' non-tail
    /// argument cells in list order. `fields` is the cons row's arity;
    /// `tail_at` the tail's bytewise position.
    fn walk_list(
        &mut self,
        sort: Chid,
        head_elem: u32,
        nil: Chid,
        cons: Chid,
        tail_at: usize,
    ) -> Result<Vec<Vec<&'a Value>>, String> {
        let mut out = Vec::new();
        let mut cur = head_elem;
        loop {
            self.step()?;
            let row = self.sole(sort, cur)?;
            if row.fun == nil {
                return Ok(out);
            }
            if row.fun != cons {
                return Err(format!(
                    "`{NAME}`: element {cur} is constructed by a fun outside the \
                     expected nil/cons pair — malformed rows, refusing"
                ));
            }
            let mut cells: Vec<&'a Value> = Vec::new();
            for (i, a) in row.args.iter().enumerate() {
                if i != tail_at {
                    cells.push(a);
                }
            }
            let tail = row.args.get(tail_at).ok_or_else(|| {
                format!("`{NAME}`: cons row arity mismatch at element {cur} — refusing")
            })?;
            out.push(cells);
            cur = self.elem(tail)?;
            if out.len() > MARKFLOW_MAX_COMPONENTS.max(MARKFLOW_MAX_CARVES) * 4 {
                return Err(format!("`{NAME}`: list beyond the walk budget — refusing"));
            }
        }
    }

    /// An interface's `(invars, outvars)` port elements.
    fn iface_ports(&mut self, iface_elem: u32) -> Result<(Vec<u32>, Vec<u32>), String> {
        let row = self.sole(self.v.iface_sort, iface_elem)?;
        if row.fun != self.v.mk_iface {
            return Err(format!(
                "`{NAME}`: element {iface_elem} is constructed by a fun outside \
                 mkIface — malformed rows, refusing"
            ));
        }
        let [invars, outvars] = row.args.as_slice() else {
            return Err(format!("`{NAME}`: mkIface row arity mismatch — refusing"));
        };
        let (iv, ov) = (self.elem(invars)?, self.elem(outvars)?);
        let ins = self
            .walk_list(self.v.portlist_sort, iv, self.v.pt_nil, self.v.pt_cons, 1)?
            .iter()
            .map(|cells| self.elem(cells[0]))
            .collect::<Result<Vec<u32>, String>>()?;
        let outs = self
            .walk_list(self.v.portlist_sort, ov, self.v.pt_nil, self.v.pt_cons, 1)?
            .iter()
            .map(|cells| self.elem(cells[0]))
            .collect::<Result<Vec<u32>, String>>()?;
        if ins.len() + outs.len() > MARKFLOW_MAX_PORTS {
            return Err(format!(
                "`{NAME}`: interface beyond the port budget ({MARKFLOW_MAX_PORTS}) — refusing"
            ));
        }
        Ok((ins, outs))
    }

    /// Resolve a PortPath element to a dense node id within `level`.
    fn resolve_portpath(&mut self, level: &Level, pp_elem: u32) -> Result<usize, String> {
        let row = self.sole(self.v.portpath_sort, pp_elem)?;
        let locate = |ports: &(Vec<u32>, Vec<u32>), port: u32| -> Result<(bool, usize), String> {
            let ins: Vec<usize> = ports
                .0
                .iter()
                .enumerate()
                .filter(|(_, p)| **p == port)
                .map(|(i, _)| i)
                .collect();
            let outs: Vec<usize> = ports
                .1
                .iter()
                .enumerate()
                .filter(|(_, p)| **p == port)
                .map(|(i, _)| i)
                .collect();
            match (ins.as_slice(), outs.as_slice()) {
                ([i], []) => Ok((false, *i)),
                ([], [j]) => Ok((true, *j)),
                ([], []) => Err(format!(
                    "`{NAME}`: a PortPath references port element {port} absent from \
                     the referenced interface — undecidable, refusing"
                )),
                _ => Err(format!(
                    "`{NAME}`: port element {port} occurs more than once on the \
                     referenced interface — ambiguous, refusing"
                )),
            }
        };
        if row.fun == self.v.pp_inner {
            let [port, pos] = row.args.as_slice() else {
                return Err(format!("`{NAME}`: ppInner row arity mismatch — refusing"));
            };
            let port = self.elem(port)?;
            let pos = match pos {
                Value::Lit(l) => match l.view() {
                    LiteralView::Nat(n) => n as usize,
                    _ => {
                        return Err(format!(
                            "`{NAME}`: `ppInner/pos` is not a Nat literal — malformed \
                             rows, refusing"
                        ))
                    }
                },
                _ => {
                    return Err(format!(
                        "`{NAME}`: `ppInner/pos` is not a literal cell — malformed rows, \
                         refusing"
                    ))
                }
            };
            let Some(ports) = level.inner_ports.get(pos) else {
                return Err(format!(
                    "`{NAME}`: ppInner position {pos} beyond the composite's {} inner \
                     systems — malformed rows, refusing",
                    level.inner_ports.len()
                ));
            };
            let (out, idx) = locate(ports, port)?;
            Ok(level.node(PNode::Inner { pos, out, idx }))
        } else if row.fun == self.v.pp_outer {
            let [port] = row.args.as_slice() else {
                return Err(format!("`{NAME}`: ppOuter row arity mismatch — refusing"));
            };
            let port = self.elem(port)?;
            let (out, idx) = locate(&level.outer_ports, port)?;
            Ok(level.node(PNode::Outer { out, idx }))
        } else {
            Err(format!(
                "`{NAME}`: element {pp_elem} is constructed by a fun outside the \
                 expected ppInner/ppOuter pair — malformed rows, refusing"
            ))
        }
    }

    /// The v1 lag classification (adjudication A-3): INSTANT iff
    /// `SysMech` ∧ stateless manifest ∧ no attached transitions.
    /// Everything else refuses with the component and case named.
    fn classify_instant(&mut self, pos: usize, sys_elem: u32) -> Result<(), String> {
        let unreadable = |case: &str| -> String {
            format!(
                "`{NAME}`: component {pos}: {case} — delivery lag not row-decidable \
                 at v1 (the latency-row lag convention is unminted); refusing, never \
                 guessing"
            )
        };
        let row = self.sole(self.v.system_sort, sys_elem)?;
        if row.fun == self.v.sys_wire {
            return Err(unreadable("nested composite (SysWire)"));
        }
        if row.fun == self.v.sys_hole {
            return Err(unreadable("open seat (SysHole) — no presentation to read"));
        }
        if row.fun != self.v.sys_mech {
            return Err(format!(
                "`{NAME}`: component {pos}: system element {sys_elem} is constructed \
                 by a fun outside the SysMech/SysWire/SysHole roster — malformed rows, \
                 refusing"
            ));
        }
        let [mech] = row.args.as_slice() else {
            return Err(format!("`{NAME}`: SysMech row arity mismatch — refusing"));
        };
        let mech = self.elem(mech)?;
        // mech_manifest {manifest, mech} — bytewise field order puts
        // the subject mech at argument index 1.
        let mrows = self.distinct_rel_rows(self.v.mech_manifest, 1, mech, 2, "mech_manifest")?;
        let manifest = match mrows.as_slice() {
            [] => {
                return Err(unreadable(
                    "mechanism content rides a species bridge (no mech_manifest row)",
                ))
            }
            [one] => self.elem(&one.args[0])?,
            _ => {
                return Err(format!(
                    "`{NAME}`: component {pos}: `mech_manifest` stated with several \
                     distinct manifests — ambiguous, refusing"
                ))
            }
        };
        let varnames_val = self
            .sole_attr(manifest, self.v.manifest_varnames, "Manifest/varnames")?
            .ok_or_else(|| {
                unreadable("manifest has no Manifest/varnames row — Moore/stateless undecidable")
            })?
            .clone();
        let varnames = self.elem(&varnames_val)?;
        let vrow = self.sole(self.v.strlist_sort, varnames)?;
        if vrow.fun == self.v.str_cons {
            return Err(unreadable("stateful (Moore) mechanism"));
        }
        if vrow.fun != self.v.str_nil {
            return Err(format!(
                "`{NAME}`: component {pos}: varnames element outside the strNil/strCons \
                 pair — malformed rows, refusing"
            ));
        }
        // sys_transition {sys, tr} — subject at index 0. ANY attached
        // transition makes the delivery timing premise-tier content.
        let trs =
            self.distinct_rel_rows(self.v.sys_transition, 0, sys_elem, 2, "sys_transition")?;
        if !trs.is_empty() {
            return Err(unreadable(
                "attached transitions (a timing law this walk has no convention to read)",
            ));
        }
        Ok(())
    }
}

/// Kosaraju SCC over `n` nodes; returns (scc id per node, id count).
/// Iterative both passes (no recursion on producer-sized graphs).
fn scc(n: usize, adj: &[Vec<usize>]) -> (Vec<usize>, usize) {
    let mut radj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (u, vs) in adj.iter().enumerate() {
        for &v in vs {
            radj[v].push(u);
        }
    }
    // pass 1: finish order
    let mut seen = vec![false; n];
    let mut order: Vec<usize> = Vec::with_capacity(n);
    for s in 0..n {
        if seen[s] {
            continue;
        }
        let mut stack: Vec<(usize, usize)> = vec![(s, 0)];
        seen[s] = true;
        while let Some(&mut (u, ref mut i)) = stack.last_mut() {
            if *i < adj[u].len() {
                let v = adj[u][*i];
                *i += 1;
                if !seen[v] {
                    seen[v] = true;
                    stack.push((v, 0));
                }
            } else {
                order.push(u);
                stack.pop();
            }
        }
    }
    // pass 2: reverse graph in reverse finish order
    let mut comp = vec![usize::MAX; n];
    let mut count = 0;
    for &s in order.iter().rev() {
        if comp[s] != usize::MAX {
            continue;
        }
        let mut stack = vec![s];
        comp[s] = count;
        while let Some(u) = stack.pop() {
            for &v in &radj[u] {
                if comp[v] == usize::MAX {
                    comp[v] = count;
                    stack.push(v);
                }
            }
        }
        count += 1;
    }
    (comp, count)
}

impl MarkflowVocab {
    /// The whole walk. Argument: the node element. See the module doc
    /// for the two columns and the v1 decided fragment.
    pub(crate) fn eval_markflow(&self, refs: &[&Value], rows: &CertRows) -> Out {
        if refs.len() != 1 {
            return Err(format!("`{NAME}` expects 1 argument, got {}", refs.len()));
        }
        let mut d = Decoder {
            v: self,
            rows,
            steps: 0,
        };
        let node = d.elem(refs[0])?;

        // ---- A-8: the ten attributes, all total ----------------------
        let components_v = d
            .need_attr(node, self.a_components, "QWireComposeMarks/components")?
            .clone();
        let wirecert_v = d
            .need_attr(node, self.a_wirecert, "QWireComposeMarks/wirecert")?
            .clone();
        let latency_v = d
            .need_attr(node, self.a_latency, "QWireComposeMarks/latency_rows")?
            .clone();
        let schedule_v = d
            .need_attr(node, self.a_schedule, "QWireComposeMarks/schedule")?
            .clone();
        let carves_v = d
            .need_attr(node, self.a_carves, "QWireComposeMarks/carves")?
            .clone();
        let carve_rows_v = d
            .need_attr(node, self.a_carve_rows, "QWireComposeMarks/carve_rows")?
            .clone();
        let diagonals_v = d
            .need_attr(node, self.a_diagonals, "QWireComposeMarks/diagonal_rows")?
            .clone();
        // presence-grade at v1: their content is other strata's.
        d.need_attr(node, self.a_proof, "QWireComposeMarks/proof")?;
        d.need_attr(node, self.a_entailment, "QWireComposeMarks/entailment")?;
        d.need_attr(node, self.a_wellposed, "QWireComposeMarks/wellposedness")?;

        // ---- components: the n citations -----------------------------
        let comp_elems: Vec<u32> = {
            let e = d.elem(&components_v)?;
            d.walk_list(self.qsatlist_sort, e, self.qsat_nil, self.qsat_cons, 1)?
                .iter()
                .map(|cells| d.elem(cells[0]))
                .collect::<Result<_, _>>()?
        };
        let n = comp_elems.len();
        if n > MARKFLOW_MAX_COMPONENTS {
            return Err(format!(
                "`{NAME}`: component count beyond the budget ({MARKFLOW_MAX_COMPONENTS}) — refusing"
            ));
        }

        // ---- the cited certificate: wiring + premise lockstep --------
        let cert = d.elem(&wirecert_v)?;
        let wiring_val = d
            .need_attr(cert, self.cert_wiring, "QWireCert/wiring")?
            .clone();
        let premises_val = d
            .need_attr(cert, self.cert_premises, "QWireCert/premises")?
            .clone();
        let n_prem = {
            let e = d.elem(&premises_val)?;
            d.walk_list(self.qspeclist_sort, e, self.qspec_nil, self.qspec_cons, 1)?
                .len()
        };
        if n_prem != n {
            return Err(format!(
                "`{NAME}`: the cited certificate declares {n_prem} premises against \
                 {n} components — positional lockstep undecidable (admission-\
                 conformance territory), refusing"
            ));
        }

        // ---- the wiring level -----------------------------------------
        let wiring = d.elem(&wiring_val)?;
        let wrow = d.sole(self.wiring_sort, wiring)?;
        if wrow.fun != self.mk_wiring {
            return Err(format!(
                "`{NAME}`: element {wiring} is constructed by a fun outside mkWiring — \
                 malformed rows, refusing"
            ));
        }
        let [w_inner, w_outer] = wrow.args.as_slice() else {
            return Err(format!("`{NAME}`: mkWiring row arity mismatch — refusing"));
        };
        let (w_inner, w_outer) = (d.elem(w_inner)?, d.elem(w_outer)?);
        let iface_elems: Vec<u32> = d
            .walk_list(self.ifacelist_sort, w_inner, self.il_nil, self.il_cons, 1)?
            .iter()
            .map(|cells| d.elem(cells[0]))
            .collect::<Result<_, _>>()?;
        if iface_elems.len() != n {
            return Err(format!(
                "`{NAME}`: the wiring declares {} inner interfaces against {n} \
                 components — positional agreement undecidable (WiringMatch \
                 territory), refusing",
                iface_elems.len()
            ));
        }
        let mut inner_ports = Vec::with_capacity(n);
        for ife in &iface_elems {
            inner_ports.push(d.iface_ports(*ife)?);
        }
        let outer_ports = d.iface_ports(w_outer)?;
        let level = Level {
            inner_ports,
            outer_ports,
        };

        // PortEq rows bound to this wiring value.
        let mut porteqs: Vec<(u32, u32)> = Vec::new();
        for row in rows.arg_rows(wiring) {
            if row.fun != self.mk_port_eq {
                continue;
            }
            let [a, b, w] = row.args.as_slice() else {
                return Err(format!("`{NAME}`: mkPortEq row arity mismatch — refusing"));
            };
            if d.elem(w)? != wiring {
                continue;
            }
            porteqs.push((d.elem(a)?, d.elem(b)?));
            if porteqs.len() > MARKFLOW_MAX_PORTEQ {
                return Err(format!(
                    "`{NAME}`: PortEq count beyond the budget ({MARKFLOW_MAX_PORTEQ}) — refusing"
                ));
            }
        }
        let mut uf = UnionFind::new(level.n_nodes());
        for (a, b) in &porteqs {
            let (na, nb) = (
                d.resolve_portpath(&level, *a)?,
                d.resolve_portpath(&level, *b)?,
            );
            uf.union(na, nb);
        }

        // ---- wire classes → the directed component graph -------------
        // per class: at most one inner-out determiner (A-2); the class
        // with a boundary-in determiner alongside an inner-out one is
        // ambiguous plumbing and refuses.
        #[derive(Default, Clone)]
        struct ClassInfo {
            drivers: Vec<usize>,   // inner positions delivering here
            driver_ports: usize,   // count of inner-out PORTS here
            outer_in: bool,        // boundary input joins this class
            consumers: Vec<usize>, // inner positions reading here
        }
        let mut classes: HashMap<usize, ClassInfo> = HashMap::new();
        for pos in 0..n {
            let (ins, outs) = (&level.inner_ports[pos].0, &level.inner_ports[pos].1);
            for idx in 0..ins.len() {
                let c = uf.find(level.node(PNode::Inner {
                    pos,
                    out: false,
                    idx,
                }));
                classes.entry(c).or_default().consumers.push(pos);
            }
            for idx in 0..outs.len() {
                let c = uf.find(level.node(PNode::Inner {
                    pos,
                    out: true,
                    idx,
                }));
                let e = classes.entry(c).or_default();
                e.driver_ports += 1;
                if !e.drivers.contains(&pos) {
                    e.drivers.push(pos);
                }
            }
        }
        for idx in 0..level.outer_ports.0.len() {
            let c = uf.find(level.node(PNode::Outer { out: false, idx }));
            classes.entry(c).or_default().outer_in = true;
        }
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
        let mut selfloop = vec![false; n];
        // class id → delivering position, for carve addressing.
        let mut class_driver: HashMap<usize, usize> = HashMap::new();
        // class id → consumers, for cycle-edge membership.
        let mut class_consumers: HashMap<usize, Vec<usize>> = HashMap::new();
        for (cid, info) in &classes {
            if info.driver_ports > 1 {
                return Err(format!(
                    "`{NAME}`: a wire class carries {} delivering ports — driven twice, \
                     the dependency graph is undecidable at this walk (directedness is \
                     qtsl_sys_causal's verdict), refusing",
                    info.driver_ports
                ));
            }
            if info.driver_ports == 1 && info.outer_in {
                return Err(format!(
                    "`{NAME}`: a wire class carries both a boundary input and a \
                     component output — ambiguous determiner, refusing"
                ));
            }
            if let [j] = info.drivers.as_slice() {
                class_driver.insert(*cid, *j);
                class_consumers.insert(*cid, info.consumers.clone());
                for &i in &info.consumers {
                    if i == *j {
                        selfloop[*j] = true;
                        if !adj[*j].contains(j) {
                            adj[*j].push(*j);
                        }
                    } else if !adj[*j].contains(&i) {
                        adj[*j].push(i);
                    }
                }
            }
        }

        // ---- decided list arithmetic BEFORE classification (A-1/A-9;
        // ---- length lies stay decided even when a component refuses) -
        let schedule: Vec<QQ> = {
            let e = d.elem(&schedule_v)?;
            d.walk_list(self.qratlist_sort, e, self.qrl_nil, self.qrl_cons, 1)?
                .iter()
                .map(|cells| d.q_lit(cells[0], "a schedule label"))
                .collect::<Result<_, _>>()?
        };
        if schedule.len() != n {
            return Ok(Err(format!(
                "schedule length {} disagrees with the demanded-mark count {n} \
                 (one label per component's mark, positional)",
                schedule.len()
            )));
        }
        for (i, t) in schedule.iter().enumerate() {
            if !t.is_nonneg() {
                return Ok(Err(format!(
                    "schedule label t[{i}] is negative — stage-space labels are \
                     nonnegative (no delivery precedes its pipe's fill)"
                )));
            }
        }
        let n_latency = {
            let e = d.elem(&latency_v)?;
            d.walk_list(self.qprooflist_sort, e, self.qpl_nil, self.qpl_cons, 1)?
                .len()
        };
        if n_latency != n {
            return Ok(Err(format!(
                "latency row count {n_latency} disagrees with the premise count {n} \
                 (each premise ships its delivery-stage arithmetic, positional)"
            )));
        }

        // carves: (wire class, gate) entries; qcvCons {gate, tail,
        // wire} in bytewise order — non-tail cells arrive [gate, wire].
        let carve_cells = {
            let e = d.elem(&carves_v)?;
            d.walk_list(self.qcarvelist_sort, e, self.qcv_nil, self.qcv_cons, 1)?
        };
        if carve_cells.len() > MARKFLOW_MAX_CARVES {
            return Err(format!(
                "`{NAME}`: carve count beyond the budget ({MARKFLOW_MAX_CARVES}) — refusing"
            ));
        }
        let n_carve_rows = {
            let e = d.elem(&carve_rows_v)?;
            d.walk_list(self.qprooflist_sort, e, self.qpl_nil, self.qpl_cons, 1)?
                .len()
        };
        if n_carve_rows != 2 * carve_cells.len() {
            return Ok(Err(format!(
                "carve_rows length {n_carve_rows} ≠ 2 × carve count {} — the \
                 containment/carved-delivery pairing (list order) is violated",
                carve_cells.len()
            )));
        }
        // resolve each carve's wire to its class; junk addressing is
        // decided false, unresolvable paths refuse.
        let mut carved_by_driver: HashMap<usize, Vec<usize>> = HashMap::new();
        let mut seen_classes: Vec<usize> = Vec::new();
        for (k, cells) in carve_cells.iter().enumerate() {
            let [_gate, wire] = cells.as_slice() else {
                return Err(format!("`{NAME}`: qcvCons row arity mismatch — refusing"));
            };
            let pp = d.elem(wire)?;
            let node_id = d.resolve_portpath(&level, pp)?;
            let cid = uf.find(node_id);
            let Some(&driver) = class_driver.get(&cid) else {
                return Ok(Err(format!(
                    "carve {k} addresses a wire no component delivers — a carve \
                     addresses its mark by the wire it rides"
                )));
            };
            if seen_classes.contains(&cid) {
                return Ok(Err(format!(
                    "two carves ride one wire class (carve {k}) — the pairing against \
                     carve_rows is ambiguous"
                )));
            }
            seen_classes.push(cid);
            carved_by_driver.entry(driver).or_default().push(cid);
        }

        // diagonal certificates: species tags in the closed genus.
        let diag_elems: Vec<u32> = {
            let e = d.elem(&diagonals_v)?;
            d.walk_list(self.qdiaglist_sort, e, self.qdg_nil, self.qdg_cons, 1)?
                .iter()
                .map(|cells| d.elem(cells[0]))
                .collect::<Result<_, _>>()?
        };
        let mut diag_kinds: Vec<&'static str> = Vec::new();
        for de in &diag_elems {
            let kind_val = d.need_attr(*de, self.diag_kind, "QDiagCert/kind")?.clone();
            let ke = d.elem(&kind_val)?;
            let krow = d.sole(self.diagkind_sort, ke)?;
            let kname = if krow.fun == self.dg_point {
                "dgPoint"
            } else if krow.fun == self.dg_enum {
                "dgEnum"
            } else if krow.fun == self.dg_contract {
                "dgContract"
            } else if krow.fun == self.dg_convex {
                "dgConvex"
            } else if krow.fun == self.dg_monotone {
                "dgMonotone"
            } else {
                return Err(format!(
                    "`{NAME}`: a QDiagCert/kind row cites a fun outside the closed \
                     five-species genus — malformed rows, refusing"
                ));
            };
            diag_kinds.push(kname);
            d.need_attr(*de, self.diag_rows, "QDiagCert/rows")?;
        }

        // ---- A-3: the v1 lag classification ---------------------------
        // (after the decided arithmetic above, so length lies decide
        // false even on nodes that refuse here)
        for (pos, comp) in comp_elems.iter().enumerate() {
            let sys_val = d.need_attr(*comp, self.qsat_sys, "QSat/sys")?.clone();
            let sys_elem = d.elem(&sys_val)?;
            d.classify_instant(pos, sys_elem)?;
        }

        // ---- stage column (all lags 0 on the decided fragment) --------
        for (j, outs) in adj.iter().enumerate() {
            for &i in outs {
                if schedule[i] != schedule[j] {
                    return Ok(Err(format!(
                        "stage row violated across instantaneous wire {j}→{i}: \
                         t[{i}] = {}/{} ≠ t[{j}] = {}/{} (label equality across \
                         instantaneous wires)",
                        schedule[i].num(),
                        schedule[i].den(),
                        schedule[j].num(),
                        schedule[j].den()
                    )));
                }
            }
        }

        // ---- carve column: the zero-lag cycle roster ------------------
        let (comp_of, n_scc) = scc(n, &adj);
        let mut members: Vec<Vec<usize>> = vec![Vec::new(); n_scc];
        for (v, &c) in comp_of.iter().enumerate() {
            members[c].push(v);
        }
        let mut nontrivial: Vec<Vec<usize>> = members
            .into_iter()
            .filter(|m| m.len() > 1 || (m.len() == 1 && selfloop[m[0]]))
            .collect();
        // canonical order: by minimal member position (A-4).
        nontrivial.sort_by_key(|m| *m.iter().min().expect("nonempty scc"));

        for (s, cyc) in nontrivial.iter().enumerate() {
            for &c in cyc {
                let covered = carved_by_driver.get(&c).is_some_and(|cids| {
                    cids.iter().any(|cid| {
                        class_consumers.get(cid).is_some_and(|cons| {
                            cons.iter()
                                .any(|i| comp_of[*i] == comp_of[c] && cyc.contains(i))
                        })
                    })
                });
                if !covered {
                    return Ok(Err(format!(
                        "mark on zero-lag cycle uncarved: component {c} (cycle {s}) \
                         has no carve on a wire it delivers into the cycle"
                    )));
                }
            }
        }
        if diag_elems.len() != nontrivial.len() {
            return Ok(Err(format!(
                "diagonal certificate count {} disagrees with the nontrivial \
                 zero-lag cycle roster ({} cycle(s) — one species-tagged \
                 certificate per cycle)",
                diag_elems.len(),
                nontrivial.len()
            )));
        }

        // ---- the v1 register (A-7): structure verified, content
        // ---- unminted — cycle-bearing nodes refuse loudly, never
        // ---- admit unchecked diagonals ---------------------------------
        if !nontrivial.is_empty() {
            return Err(format!(
                "`{NAME}`: zero-lag cycle structure verified ({} cycle(s); carves, \
                 pairing, and diagonal tags [{}] present) — diagonal species \
                 content and containment/carved-delivery row content are not yet \
                 recomputable (species row conventions unminted; the v1 loud-defer \
                 register); refusing, never admitting unchecked",
                nontrivial.len(),
                diag_kinds.join(", ")
            ));
        }

        Ok(Ok(()))
    }
}

#[cfg(test)]
mod tests {
    use super::scc;

    #[test]
    fn scc_two_cycle_and_tail() {
        // 0→1, 1→0 (a 2-cycle), 2→0 (a tail into it), 3 isolated.
        let adj = vec![vec![1], vec![0], vec![0], vec![]];
        let (comp, count) = scc(4, &adj);
        assert_eq!(comp[0], comp[1]);
        assert_ne!(comp[0], comp[2]);
        assert_ne!(comp[0], comp[3]);
        assert_eq!(count, 3);
    }

    #[test]
    fn scc_line_is_all_trivial() {
        let adj = vec![vec![1], vec![2], vec![]];
        let (comp, count) = scc(3, &adj);
        assert_eq!(count, 3);
        assert!(comp[0] != comp[1] && comp[1] != comp[2]);
    }
}
