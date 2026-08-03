//! `qtsl_wire_causality`: the causality walk — the ∀-face ranks
//! recompute, demanded on every `QWireCompose` node (the composition
//! family's safety face; the MarkFlow walk in [`crate::markflow`] is
//! its ∃-dual, and the theory registers the two side by side in the
//! recompute registry).
//!
//! Semantic authority: the Qtsl theory's QWireCompose block (the
//! declaration comment above `qtsl_wire_causality`: "from the node's
//! components and ranks and the cited certificate's wiring, one rank
//! per component and strict rank increase along every directed wire —
//! no cyclic wiring can PASS the walk. Bounded recompute over the
//! node's declaration closure, never chase derivation; demanded on
//! every instance" — `ax/wf/qwirecompose_causality`), and the frozen
//! oracle-registry spec (the c4 registry):
//! the walk checks the declared rank shadow against the wiring under
//! certification, one stratum down from `qtsl_sys_causal` (which
//! walks the System composite's own dependency relation). Producer
//! twin: mtk-catalogue `QAGComposeRow.causality_rank` (one `u64` per
//! component; strict increase along the wiring is THIS recompute —
//! the declared ranks are its shadow).
//!
//! # The walk
//!
//! From the node's closure alone: the components list fixes `n`; the
//! cited `QWireCert`'s wiring fixes the directed component graph
//! (edges `j→i` per PortEq wire class with the inner-out determiner
//! at position `j` and an inner-in member at position `i` — the
//! [`crate::markflow`] class machinery verbatim, minus the lag
//! classification: causality constrains EVERY directed wire, so
//! there is no instant-subgraph carve and no unminted row content
//! anywhere in the walk); the ranks list supplies one natural per
//! component. Verdicts:
//!
//! - **decided FALSE, named** — ranks length ≠ components length
//!   ("one rank per component" is this walk's own list-shape
//!   obligation, the inc-3 A-1 precedent; decided BEFORE the wiring
//!   stages, so the length lie stays decided even on nodes whose
//!   wiring would refuse); a wire `j→i` with `rank[j] ≥ rank[i]`
//!   (ties included), the edge and both ranks named; a self-loop
//!   wire (strict increase at `j→j` is unsatisfiable — the smallest
//!   cyclic wiring, killed by the same edge-local check that kills
//!   every larger cycle: a cycle cannot carry strictly increasing
//!   ranks, so no cycle detector is needed for the verdict).
//! - **REFUSED, named** — the registry spec's own arity clause
//!   ("a component/rank arity mismatch against the wiring's
//!   inner-system count refuses"): components vs the wiring's
//!   declared inner-interface count is WiringMatch territory, and
//!   components vs the certificate's premise count is
//!   admission-conformance territory — both are other relations'
//!   verdicts to fail, so this walk refuses rather than
//!   double-adjudicating. Likewise driven-twice wire classes,
//!   boundary-input/component-output determiner ambiguity, missing
//!   attribute rows, undecodable spines, and budget excess.
//!
//! Ranks are naturals with no width ceiling evaluator-side: both
//! `Nat` and multiprec `NatBig` literal cells decode (to `BigUint`);
//! the producer's `Vec<u64>` is its own budget, never the checker's
//! assumption. Decided violations surface through the provider's
//! named-violations register (the walk-evaluator design memo F-4),
//! exactly as the markflow family's do. No store dependency.

use crate::roster::{EntryRow, RelKind};
use crate::rowctx::{CertRows, CtorRow};
use crate::theory::{Chid, DomainSig, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use num_bigint::BigUint;
use std::collections::HashMap;

/// The causality family's row of the claimed roster (appended LAST at
/// registration — provider.rs; every existing roster position is
/// unchanged).
pub(crate) const ENTRIES: &[EntryRow] = &[(
    "qtsl_wire_causality",
    &[("node", "QWireCompose")],
    RelKind::WireCausality,
)];

/// Budgets: refusal beyond, never divergence.
pub const WIRECAUSALITY_MAX_COMPONENTS: usize = 1 << 10;
pub const WIRECAUSALITY_MAX_PORTS: usize = 1 << 12;
pub const WIRECAUSALITY_MAX_PORTEQ: usize = 1 << 14;
const MAX_DECODE_STEPS: usize = 1 << 20;

// ---------------------------------------------------------------------
// Vocabulary
// ---------------------------------------------------------------------

/// The composition-node vocabulary, pinned at resolution (names
/// select, shapes verify, identities pin). A production index deriving
/// a different shape fails resolution — the family is then not claimed
/// (safe-fail), never mis-decoded.
#[derive(Debug, Clone)]
pub struct WireCausalityVocab {
    // the node's five attributes
    a_proof: Chid,
    a_components: Chid,
    a_wirecert: Chid,
    a_ranks: Chid,
    a_wellposed: Chid,
    // satisfaction citations (spine only — QSat content is other
    // strata's)
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
    // the rank spine
    qnatlist_sort: Chid,
    qnl_nil: Chid,
    qnl_cons: Chid,
    /// Per-sort constructor rosters for the value-like sorts the walk
    /// `sole`-resolves on: sort chid → (fun chid → domain).
    ctors: HashMap<Chid, HashMap<Chid, DomainSig>>,
}

/// Build the composition-node vocabulary. `Err` → the family is not
/// claimed (C-ORACLE safe-fail; reason recorded on the provider's
/// notes).
pub fn build_wirecausality_vocab(indices: &[&TheoryIndex]) -> Result<WireCausalityVocab, String> {
    let sort = |name: &str| -> Result<Chid, String> {
        for index in indices {
            if let Some(c) = index.sort(name) {
                return Ok(c);
            }
        }
        Err(format!("no `{name}` sort among the swept revisions"))
    };
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

    let node_sort = sort("QWireCompose")?;
    let qsatlist_sort = sort("QSatList")?;
    let cert_sort = sort("QWireCert")?;
    let qspeclist_sort = sort("QSpecList")?;
    let wiring_sort = sort("Wiring")?;
    let portpath_sort = sort("PortPath")?;
    let iface_sort = sort("Iface")?;
    let ifacelist_sort = sort("IfaceList")?;
    let portlist_sort = sort("PortList")?;
    let qnatlist_sort = sort("QNatList")?;
    let qprooflist_sort = sort("QProofList")?;

    let need = |name: &str, got: &SortKey, want: Chid| -> Result<(), String> {
        if *got == SortKey::Elem(want) {
            Ok(())
        } else {
            Err(format!("`{name}`: codomain is not the expected sort"))
        }
    };

    let (a_proof, _) = attr("QWireCompose/proof", node_sort)?;
    let (a_components, c) = attr("QWireCompose/components", node_sort)?;
    need("QWireCompose/components", &c, qsatlist_sort)?;
    let (a_wirecert, c) = attr("QWireCompose/wirecert", node_sort)?;
    need("QWireCompose/wirecert", &c, cert_sort)?;
    let (a_ranks, c) = attr("QWireCompose/ranks", node_sort)?;
    need("QWireCompose/ranks", &c, qnatlist_sort)?;
    let (a_wellposed, c) = attr("QWireCompose/wellposedness", node_sort)?;
    need("QWireCompose/wellposedness", &c, qprooflist_sort)?;

    let (cert_wiring, c) = attr("QWireCert/wiring", cert_sort)?;
    need("QWireCert/wiring", &c, wiring_sort)?;
    let (cert_premises, c) = attr("QWireCert/premises", cert_sort)?;
    need("QWireCert/premises", &c, qspeclist_sort)?;

    let mut ctors: HashMap<Chid, HashMap<Chid, DomainSig>> = HashMap::new();
    let mut add = |sort: Chid, pair: (Chid, DomainSig)| -> Chid {
        ctors.entry(sort).or_default().insert(pair.0, pair.1);
        pair.0
    };

    let qsat_nil = add(qsatlist_sort, ctor("qsatNil", qsatlist_sort)?);
    let qsat_cons = add(qsatlist_sort, ctor("qsatCons", qsatlist_sort)?);
    let qspec_nil = add(qspeclist_sort, ctor("qspecNil", qspeclist_sort)?);
    let qspec_cons = add(qspeclist_sort, ctor("qspecCons", qspeclist_sort)?);
    let qnl_nil = add(qnatlist_sort, ctor("qnlNil", qnatlist_sort)?);
    let qnl_cons = add(qnatlist_sort, ctor("qnlCons", qnatlist_sort)?);
    let mk_wiring = add(wiring_sort, ctor("mkWiring", wiring_sort)?);
    let mk_port_eq = add(sort("PortEq")?, ctor("mkPortEq", sort("PortEq")?)?);
    let pp_inner = add(portpath_sort, ctor("ppInner", portpath_sort)?);
    let pp_outer = add(portpath_sort, ctor("ppOuter", portpath_sort)?);
    let mk_iface = add(iface_sort, ctor("mkIface", iface_sort)?);
    let il_nil = add(ifacelist_sort, ctor("ilNil", ifacelist_sort)?);
    let il_cons = add(ifacelist_sort, ctor("ilCons", ifacelist_sort)?);
    let pt_nil = add(portlist_sort, ctor("ptNil", portlist_sort)?);
    let pt_cons = add(portlist_sort, ctor("ptCons", portlist_sort)?);

    Ok(WireCausalityVocab {
        a_proof,
        a_components,
        a_wirecert,
        a_ranks,
        a_wellposed,
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
        qnatlist_sort,
        qnl_nil,
        qnl_cons,
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

/// Port-space node ids for one composite level (single level — the
/// composition node cites one wiring; nested composites are their own
/// QWireCompose nodes with their own demands).
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
    v: &'a WireCausalityVocab,
    rows: &'a CertRows,
    steps: usize,
}

const NAME: &str = "qtsl_wire_causality";

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

    /// A rank cell: a natural with no width ceiling (`Nat` and
    /// multiprec `NatBig` both decode — the producer's `u64` is its
    /// own budget, never the checker's assumption).
    fn nat_lit(&self, val: &Value, what: &str) -> Result<BigUint, String> {
        match val {
            Value::Lit(l) => match l.view() {
                LiteralView::Nat(n) => Ok(BigUint::from(n)),
                LiteralView::NatBig(bytes) => Ok(BigUint::from_bytes_le(bytes)),
                _ => Err(format!(
                    "`{NAME}`: {what} is not a Nat literal — malformed rows, refusing"
                )),
            },
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

    /// Walk a nil/cons list, returning the cons rows' non-tail
    /// argument cells in list order. `tail_at` is the tail's bytewise
    /// position.
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
            if out.len() > WIRECAUSALITY_MAX_COMPONENTS * 4 {
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
        if ins.len() + outs.len() > WIRECAUSALITY_MAX_PORTS {
            return Err(format!(
                "`{NAME}`: interface beyond the port budget ({WIRECAUSALITY_MAX_PORTS}) — refusing"
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
}

impl WireCausalityVocab {
    /// The whole walk. Argument: the node element. See the module doc
    /// for the verdict roster.
    pub(crate) fn eval_wire_causality(&self, refs: &[&Value], rows: &CertRows) -> Out {
        if refs.len() != 1 {
            return Err(format!("`{NAME}` expects 1 argument, got {}", refs.len()));
        }
        let mut d = Decoder {
            v: self,
            rows,
            steps: 0,
        };
        let node = d.elem(refs[0])?;

        // ---- field presence: the five attributes, all total ----------
        let components_v = d
            .need_attr(node, self.a_components, "QWireCompose/components")?
            .clone();
        let wirecert_v = d
            .need_attr(node, self.a_wirecert, "QWireCompose/wirecert")?
            .clone();
        let ranks_v = d
            .need_attr(node, self.a_ranks, "QWireCompose/ranks")?
            .clone();
        // presence-grade: their content is other strata's.
        d.need_attr(node, self.a_proof, "QWireCompose/proof")?;
        d.need_attr(node, self.a_wellposed, "QWireCompose/wellposedness")?;

        // ---- components: the n citations ------------------------------
        let n = {
            let e = d.elem(&components_v)?;
            d.walk_list(self.qsatlist_sort, e, self.qsat_nil, self.qsat_cons, 1)?
                .len()
        };
        if n > WIRECAUSALITY_MAX_COMPONENTS {
            return Err(format!(
                "`{NAME}`: component count beyond the budget \
                 ({WIRECAUSALITY_MAX_COMPONENTS}) — refusing"
            ));
        }

        // ---- decided list arithmetic FIRST (the inc-3 A-1 ordering:
        // ---- the length lie stays decided even on nodes whose wiring
        // ---- stages would refuse) --------------------------------------
        let ranks: Vec<BigUint> = {
            let e = d.elem(&ranks_v)?;
            d.walk_list(self.qnatlist_sort, e, self.qnl_nil, self.qnl_cons, 1)?
                .iter()
                .map(|cells| d.nat_lit(cells[0], "a causality rank"))
                .collect::<Result<_, _>>()?
        };
        if ranks.len() != n {
            return Ok(Err(format!(
                "ranks length {} disagrees with the component count {n} (one rank \
                 per component, positional)",
                ranks.len()
            )));
        }

        // ---- the cited certificate: wiring + premise lockstep ---------
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

        // ---- the wiring level ------------------------------------------
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
            // the registry spec's own arity clause: component/rank
            // arity vs the wiring's inner-system count REFUSES
            // (WiringMatch territory — another relation's verdict to
            // fail, never double-adjudicated here).
            return Err(format!(
                "`{NAME}`: the wiring declares {} inner interfaces against {n} \
                 components — component/rank arity vs the wiring's inner-system \
                 count is WiringMatch territory, refusing",
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
            if porteqs.len() > WIRECAUSALITY_MAX_PORTEQ {
                return Err(format!(
                    "`{NAME}`: PortEq count beyond the budget \
                     ({WIRECAUSALITY_MAX_PORTEQ}) — refusing"
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

        // ---- wire classes → the directed component graph --------------
        // per class: at most one inner-out determiner; a class with a
        // boundary-in determiner alongside an inner-out one is
        // ambiguous plumbing and refuses (the markflow A-2 machinery
        // verbatim).
        #[derive(Default, Clone)]
        struct ClassInfo {
            drivers: Vec<usize>,
            driver_ports: usize,
            outer_in: bool,
            consumers: Vec<usize>,
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
        let mut edges: Vec<(usize, usize)> = Vec::new();
        for info in classes.values() {
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
                for &i in &info.consumers {
                    if !edges.contains(&(*j, i)) {
                        edges.push((*j, i));
                    }
                }
            }
        }

        // ---- the strict-increase check (edge-local; a cycle cannot
        // ---- carry strictly increasing ranks, so no cycle detector
        // ---- is needed for the verdict) ---------------------------------
        for (j, i) in &edges {
            if j == i {
                return Ok(Err(format!(
                    "causality rank must strictly increase along directed wire \
                     {j}→{i}: a self-delivering wire is the smallest cyclic wiring — \
                     no cyclic wiring can pass the walk"
                )));
            }
            if ranks[*j] >= ranks[*i] {
                return Ok(Err(format!(
                    "causality rank must strictly increase along directed wire \
                     {j}→{i}: rank[{j}] = {} ≥ rank[{i}] = {}",
                    ranks[*j], ranks[*i]
                )));
            }
        }

        Ok(Ok(()))
    }
}
