"""Reference checker for the Bernstein Logic v0 toy (v0 reference).

A SymPy/exact-Q realization of the check-side semantics: for every proof
node, verify the applicability side-conditions the geolog contract states
(designv3/PiecewisePolynomialLogicCertificate.geolog), plus hypernet
well-formedness and SP_H synthesis-and-compare (BUILD-PLAN B4: the sp
conjunction is synthesized from the hypernet and VERIFIED against the
certificate's root pre, never trusted).

This is the exact-Q oracle of BUILD-PLAN 5.3 — the top of the proptest
chain the Rust/Lean legs will differential-test against.  It is NOT the
verified checker (that is legs B–D, in Lean); it is the executable spec the
mutation battery (mutants.py) exercises as the checker legs' acceptance
oracle.

Every failure carries a stable check-id string; mutants assert on these.
"""

from __future__ import annotations

import sympy as sp
from sympy import Rational

from bl_cert import (
    TEinsum, TPoly, barycentric_exprs, tpoly_to_sympy, tpoly_wf_errors,
    FAnd, FAtom, FFalse, FInRegion, FOr, FTrue, Formula, HOLE, Hypernet,
    Judgment, PAndE, PAndI, PArithAtom, PAx, PBernCone, PCast, PCell,
    PConvElim, PConvIntro, PCopy, PCut, PDelete, PEqElim, PEqRefl, PEqSym,
    PConstExact, PFarkas, PLiRPA, PNorm, POrECtx, PPoly, PPromise,
    PReLUAbove, PReLUNN, PReLUNeg, PReLUPos, PRelu, PReluUnfold, Proof,
    PSyzygy, TNeg,
    BlockLattice, FamBlock, FamJudgment, PProductLattice, subst_tree,
    product_lattice_blocks,
    ENC_FUNCS, EncJudgment, PEnclosure,
    JetFrame, JDiv, JEvo, PJetDiv, PFunctionalDeriv, PIntMono,
    RELU_UNFOLD_ARITY, relu_expansion_spfacts,
    Simplex, TAdd, TConst, TMul, TSub, TVar, Term,
    apply_predicate, barycentric_halfspace_form, canon_sympy, canon_term,
    conj_get, conj_replace, formula_free_wires, formula_subst,
    idx_symbol_name, prim_inputs, prim_outputs, sp_H, term_free_wires,
    term_idx_profile, term_to_sympy, wire_of_sym_from,
)
from bl_bernstein import bernstein_coeffs, berncone_grid, barycentric_coords


class Failures(list):
    def add(self, check_id: str, where: str, detail: str):
        self.append((check_id, where, detail))


# =========================================================================
# hypernet well-formedness
# =========================================================================

def check_hypernet(h: Hypernet, fails: Failures):
    wires = {w.name: w for w in h.wires}
    if len(wires) != len(h.wires):
        fails.add("wf.wire-dup", "hypernet", "duplicate wire names")

    # Reserved coordinate namespace (X2 design-review F-001): the pinned
    # symbol convention maps TIdx(TVar(w), i) to the name "<w>__<i>", so
    # a LITERAL wire of that shape would alias an indexed coordinate in
    # both the canonical and value-exact combination replays — Lean's
    # wireCoordKey translation is injective, and the mirror keeps it so
    # by excluding the collision domain at declaration.
    import re as _re
    for w in h.wires:
        if _re.fullmatch(r".*__\d+", w.name):
            fails.add("wf.reserved-name", f"wire {w.name}",
                      "wire names of the form <base>__<digits> are "
                      "reserved for the TIdx coordinate symbol namespace")
        if w.name == HOLE:
            # Lean Certificate.holeFresh (X2 design-review F-008): the
            # predicate placeholder is never a diagram wire.
            fails.add("wf.hole-wire", f"wire {w.name}",
                      "the predicate hole cannot be declared as a wire")

    producers = {}
    consumers = {}
    for idx, p in enumerate(h.prims):
        for w in prim_inputs(p):
            if w not in wires:
                fails.add("wf.unknown-wire", f"prim[{idx}]", f"input {w}")
                continue
            consumers.setdefault(w, []).append(idx)
        for w in prim_outputs(p):
            if w not in wires:
                fails.add("wf.unknown-wire", f"prim[{idx}]", f"output {w}")
                continue
            producers.setdefault(w, []).append(idx)

    # linearity (Alvarez-Picallo hypernet conditions, paper sec:geolog)
    for w, cs in consumers.items():
        if len(cs) > 1:
            fails.add("wf.linearity", f"wire {w}", f"consumed by prims {cs}")
    for w, ps in producers.items():
        if len(ps) > 1:
            fails.add("wf.linearity", f"wire {w}", f"produced by prims {ps}")

    # inputs are not produced; non-inputs are produced exactly once
    for w in h.inputs:
        if w in producers:
            fails.add("wf.input-produced", f"wire {w}", "declared input has a producer")
    for w in wires:
        if w not in h.inputs and w not in producers:
            fails.add("wf.orphan-wire", f"wire {w}", "no producer and not an input")

    # acyclicity via topological order on prims
    order, placed = [], set(h.inputs)
    remaining = list(range(len(h.prims)))
    progress = True
    while remaining and progress:
        progress = False
        for idx in list(remaining):
            if all(w in placed for w in prim_inputs(h.prims[idx])):
                placed.update(prim_outputs(h.prims[idx]))
                order.append(idx)
                remaining.remove(idx)
                progress = True
    if remaining:
        fails.add("wf.acyclicity", "hypernet", f"cyclic or unproducible prims {remaining}")

    # dtype schemas per primitive
    def dt(w):
        return wires[w].dtype if w in wires else None

    for idx, p in enumerate(h.prims):
        where = f"prim[{idx}]:{type(p).__name__}"
        if isinstance(p, PCopy):
            if any(dt(o) != dt(p.inp) for o in p.outs):
                fails.add("wf.dtype", where, "copy must preserve dtype")
        elif isinstance(p, PPoly):
            if dt(p.out) != "Q" or any(dt(i) != "Q" for i in p.inps):
                fails.add("wf.dtype", where, "Poly is Q -> Q in the v0 toy")
            if not term_free_wires(p.q) <= set(p.inps):
                fails.add("wf.poly-scope", where, "q mentions non-input wires")
        elif isinstance(p, PCell):
            if dt(p.inp) != "Q":
                fails.add("wf.dtype", where, "Cell input must be Q (embeds in R)")
            if any(dt(o) != "B" for o in p.outs):
                fails.add("wf.dtype", where, "Cell outputs must be B (sec:cell-prim)")
            if len(p.outs) != len(p.cells):
                fails.add("wf.cell-arity", where, "one indicator wire per cell")
            check_complex(p.cells, fails, where)
        elif isinstance(p, PCast):
            if not (dt(p.inp) == "B" and dt(p.out) == "Q"):
                fails.add("wf.dtype", where, "v0 Cast is B -> Q only")
        elif isinstance(p, PRelu):
            # terms-v1 discharged-warrant profile: both ports Q (the toy's
            # scalar wires ARE shape [1]; BINARY.md sec 5.2 profile gate).
            if not (dt(p.preact) == "Q" and dt(p.post) == "Q"):
                fails.add("wf.dtype", where,
                          "packaged relu ports must both be Q "
                          "(terms-v1 [1]/Q profile)")


def cell_interval(cell):
    """1D region-encoded cell -> (lo, hi) with sympy -oo/oo endpoints."""
    (a,), (b,) = cell.simplex.vertices
    a, b = Rational(a), Rational(b)
    if a == b:
        raise ValueError("degenerate cell simplex")
    if a > b:
        a, b = b, a
        Smap = {0: 1, 1: 0}
        S = frozenset(Smap[i] for i in cell.S)
    else:
        S = cell.S
    # conv(a,b), a<b: lambda_0 = (b-x)/(b-a), lambda_1 = (x-a)/(b-a)
    if S == frozenset():
        return (a, b)
    if S == frozenset({0}):
        return (b, sp.oo)   # lambda_0 <= 0  <=>  x >= b
    if S == frozenset({1}):
        return (-sp.oo, a)  # lambda_1 <= 0  <=>  x <= a
    raise ValueError("S must be a proper subset of {0,1} in 1D")


def check_complex(cells, fails: Failures, where: str):
    """1D covering + conformity for region-encoded cell complexes (S2).
    Covering: union of closed cells is all of R (no gaps).  Conformity:
    cell interiors are pairwise disjoint (overlap only in boundary points)."""
    try:
        ivs = sorted(cell_interval(c) for c in cells)
    except ValueError as e:
        fails.add("wf.cell-degenerate", where, str(e))
        return
    # covering
    if ivs[0][0] != -sp.oo or ivs[-1][1] != sp.oo:
        fails.add("wf.cell-covering", where, f"cells do not cover R: {ivs}")
    for (l1, h1), (l2, h2) in zip(ivs, ivs[1:]):
        if h1 < l2:
            fails.add("wf.cell-covering", where, f"gap between {h1} and {l2}")
        if h1 > l2:
            fails.add("wf.cell-conformity", where,
                      f"interior overlap between cells ending {h1} / starting {l2}")


# =========================================================================
# predicate shape classifiers (BUILD-PLAN D1 closed enumeration, v0 slice)
# =========================================================================

def _pred_atoms(pred: Formula):
    if isinstance(pred, FAnd):
        return _pred_atoms(pred.l) + _pred_atoms(pred.r)
    return [pred]


def _atom_hole_const(a: Formula):
    """Return (op, const, side) for atoms (hole op const) / (const op hole)."""
    if not isinstance(a, FAtom):
        return None
    if a.l == TVar(HOLE) and isinstance(a.r, TConst):
        return (a.op, a.r.value, "l")
    if a.r == TVar(HOLE) and isinstance(a.l, TConst):
        return (a.op, a.l.value, "r")
    return None


def is_convex_predicate(pred: Formula) -> bool:
    """v0 enumeration: conjunctions of non-strict scalar atoms hole-vs-const."""
    for a in _pred_atoms(pred):
        m = _atom_hole_const(a)
        if m is None or m[0] not in ("<=", ">=", "="):
            return False
    return True


def is_conic_predicate(pred: Formula) -> bool:
    """v0 enumeration: conjunctions of non-strict scalar atoms vs ZERO."""
    for a in _pred_atoms(pred):
        m = _atom_hole_const(a)
        if m is None or m[0] not in ("<=", ">=", "=") or m[1] != 0:
            return False
    return True


def eval_ground_formula(f: Formula) -> bool:
    """Exact evaluation of a wire-free formula (used on predicate instances)."""
    if isinstance(f, FTrue):
        return True
    if isinstance(f, FFalse):
        return False
    if isinstance(f, FAnd):
        return eval_ground_formula(f.l) and eval_ground_formula(f.r)
    if isinstance(f, FOr):
        return eval_ground_formula(f.l) or eval_ground_formula(f.r)
    if isinstance(f, FAtom):
        sym = {}
        lv, rv = term_to_sympy(f.l, sym), term_to_sympy(f.r, sym)
        if sym:
            raise ValueError("eval_ground_formula on non-ground atom")
        lv, rv = sp.Rational(sp.expand(lv)), sp.Rational(sp.expand(rv))
        return {"<=": lv <= rv, "<": lv < rv, "=": lv == rv,
                ">=": lv >= rv, ">": lv > rv}[f.op]
    raise TypeError(f)


def conjunct_list(f: Formula) -> list:
    """Flattened AND-tree conjuncts (Lean `Formula.conjunctList`)."""
    if isinstance(f, FAnd):
        return conjunct_list(f.l) + conjunct_list(f.r)
    return [f]


def premise_contains(pre: Formula, sub: Formula) -> bool:
    """Conjunct-wise premise containment (Lean `premiseContains`): every
    conjunct of `sub` is a conjunct of `pre` — the decoupling that lets a
    component proved over its own box enter a composite whose premise
    merely CONTAINS that box."""
    pre_cs = conjunct_list(pre)
    return all(any(a == b for b in pre_cs) for a in conjunct_list(sub))


def syzygy_conclusion_form(conclusion: Term, post: Formula) -> bool:
    """Lean `syzygyConclusionForm` (Core/Catalogue.lean), field-for-field:
    the interchangeable readings of the value-exact bound
    (conclusion <= 0), CORE vocabulary owned by PSyzygy (ratified
    2026-07-18; the wire/python parity pass adopted the widened core
    reading 2026-07-19 — before that this checker pinned the zero-normal
    form only).  Each reading is semantically equivalent to
    (conclusion <= 0); the Lean transport is
    `holds_of_syzygyConclusionForm` inside `sound_syzygy`:
      (Z<=) zero-form:  post = (conclusion <= 0)
      (G)   ge-flip:    conclusion = TNeg(e), post = (e >= 0)
      (L<=) literal:    conclusion = TSub(l, r), post = (l <= r)"""
    if post == FAtom("<=", conclusion, TConst(Rational(0))):
        return True
    if isinstance(conclusion, TNeg) and \
            post == FAtom(">=", conclusion.t, TConst(Rational(0))):
        return True
    if isinstance(conclusion, TSub) and \
            post == FAtom("<=", conclusion.l, conclusion.r):
        return True
    return False


# =========================================================================
# the ReLU port-lookup linkage (register 1; Lean `reluLinked`)
# =========================================================================
#
# The five ReLU/LiRPA rules and the unfold rule cite the DIAGRAM: their
# side condition is a port lookup over the certificate's hypernet
# (`reluLinked H preact post` — one line, decidable; Lean
# Core/Catalogue.lean, B12 realized).  check_proof's recursion does not
# thread the hypernet (it predates diagram-citing rules), so the
# certificate-global hypernet is published module-level by
# check_certificate around the proof walk — same pattern as the scope
# memo (an execution detail, not a semantics change: the hypernet IS
# certificate-global).  Standalone rule tests set it explicitly.

import threading as _threading

_LINKAGE = _threading.local()

# Obligation U's rule is realized executable-side ahead of its staged
# Lean constructor (X2 design-review F-004): the certified surface stays
# aligned with the staged calculus by default — accepting a certificate
# that USES PReluUnfold requires this explicit opt-in (tests flip it;
# no producer emits the rule yet).
ALLOW_UNSTAGED_UNFOLD = False


def set_linkage_hypernet(h):
    # Thread-local (X2 design-review F-003): a process-global let a
    # concurrent check validate a ReLU rule against another
    # certificate's hypernet.  Publication is per-thread and cleared in
    # check_certificate's finally; re-entrant same-thread checks remain
    # out of contract (as before).
    _LINKAGE.H = h


def _linkage_hypernet():
    return getattr(_LINKAGE, "H", None)


def relu_linked(h, preact: str, post: str) -> bool:
    """Lean `reluLinked`: a packaged relu application at exactly these
    ports.  (The positive-total-size gate is structural in the toy —
    PRelu is scalar by construction.)"""
    return h is not None and any(
        isinstance(p, PRelu) and p.preact == preact and p.post == post
        for p in h.prims)


def _linkage_check(preact, post, fails, where, rule):
    h = _linkage_hypernet()
    if h is None:
        fails.add(f"{rule}.no-hypernet", where,
                  "no linkage hypernet published (set_linkage_hypernet)")
        return False
    if not relu_linked(h, preact, post):
        fails.add(f"{rule}.linkage", where,
                  f"no packaged relu application at ports "
                  f"({preact}, {post}) — reluLinked fails")
        return False
    return True


# =========================================================================
# proof checking
# =========================================================================

def check_proof(node: Proof, wire_names: set, fails: Failures, where="root"):
    if isinstance(node, PProductLattice):
        # family-v1: concludes is a FamJudgment, not a sequent — the
        # family layer's own checks apply (BINARY.md SS6.2 tag 27).
        check_product_lattice(node, fails, where)
        return
    if isinstance(node, PEnclosure):
        # enclosure-v1: concludes is an EncJudgment, not a sequent —
        # the remainder-bound rule's own check applies (encCheck,
        # BINARY.md SS6.2 tag 28).
        check_enclosure(node, fails, where)
        return
    if isinstance(node, PJetDiv):
        # jet-v1: concludes is a JDiv jet judgement (sibling sort) — the
        # D_x recompute applies ([J1], jet-v1 contract §3). Root-only.
        check_jet_div(node, wire_names, fails, where)
        return
    if isinstance(node, PFunctionalDeriv):
        # jet-v1: concludes is a JEvo jet judgement — the R1 recompute
        # applies ([J2]). Root-only.
        check_functional_deriv(node, wire_names, fails, where)
        return
    c = node.concludes
    for side, f in (("pre", c.pre), ("post", c.post)):
        extra = formula_free_wires(f) - wire_names
        if extra:
            fails.add("wf.formula-scope", f"{where}.{side}",
                      f"unknown wires {sorted(extra)}")

    if isinstance(node, PAx):
        if c.pre != c.post:
            fails.add("ax.pre-post", where, "PAx requires pre == post")
        return

    if isinstance(node, PAndE):
        check_proof(node.premise, wire_names, fails, where + ".premise")
        pj = node.premise.concludes
        if pj.pre != c.pre:
            fails.add("ande.pre", where, "premise pre != conclusion pre")
        if not isinstance(pj.post, FAnd):
            fails.add("ande.not-and", where, "premise post is not a conjunction")
        else:
            want = pj.post.l if node.which == "l" else pj.post.r
            if c.post != want:
                fails.add("ande.post", where, "conclusion is not the selected conjunct")
        return

    if isinstance(node, PAndI):
        check_proof(node.l, wire_names, fails, where + ".l")
        check_proof(node.r, wire_names, fails, where + ".r")
        if node.l.concludes.pre != c.pre or node.r.concludes.pre != c.pre:
            fails.add("andi.pre", where, "premise pre mismatch")
        if c.post != FAnd(node.l.concludes.post, node.r.concludes.post):
            fails.add("andi.post", where, "post != And(l.post, r.post)")
        return

    if isinstance(node, POrECtx):
        check_proof(node.left, wire_names, fails, where + ".left")
        check_proof(node.right, wire_names, fails, where + ".right")
        try:
            disj = conj_get(c.pre, node.path)
        except KeyError as e:
            fails.add("orectx.path", where, str(e))
            return
        if not isinstance(disj, FOr):
            fails.add("orectx.path-not-or", where,
                      f"conjunct at path is {type(disj).__name__}, not FOr")
            return
        if node.left.concludes.pre != conj_replace(c.pre, node.path, disj.l):
            fails.add("orectx.left-pre", where, "left pre != pre[path := left disjunct]")
        if node.right.concludes.pre != conj_replace(c.pre, node.path, disj.r):
            fails.add("orectx.right-pre", where, "right pre != pre[path := right disjunct]")
        if node.left.concludes.post != c.post or node.right.concludes.post != c.post:
            fails.add("orectx.post", where, "branch posts must equal conclusion post")
        return

    if isinstance(node, PCut):
        check_proof(node.left, wire_names, fails, where + ".left")
        check_proof(node.right, wire_names, fails, where + ".right")
        if node.left.concludes.pre != c.pre:
            fails.add("cut.pre", where, "left premise pre != conclusion pre")
        if node.left.concludes.post != node.cutFormula:
            fails.add("cut.left-post", where, "left post != cut formula")
        if node.right.concludes.pre != FAnd(node.left.concludes.pre, node.cutFormula):
            fails.add("cut.right-pre", where,
                      "right pre != And(left pre, cut formula)")
        if node.right.concludes.post != c.post:
            fails.add("cut.post", where, "right post != conclusion post")
        return

    if isinstance(node, PEqRefl):
        # post = (term = term); pre arbitrary (Norm convention).
        if c.post != FAtom("=", node.term, node.term):
            fails.add("eqrefl.post", where, "post != (term = term)")
        return

    if isinstance(node, PEqSym):
        check_proof(node.premise, wire_names, fails, where + ".premise")
        if node.premise.concludes.pre != c.pre:
            fails.add("eqsym.pre", where, "premise pre mismatch")
        if node.premise.concludes.post != FAtom("=", node.termT, node.termU):
            fails.add("eqsym.premise-post", where, "premise post != (t = u)")
        if c.post != FAtom("=", node.termU, node.termT):
            fails.add("eqsym.post", where, "post != (u = t)")
        return

    if isinstance(node, PEqElim):
        check_proof(node.eq, wire_names, fails, where + ".eq")
        check_proof(node.body, wire_names, fails, where + ".body")
        if node.eq.concludes.pre != c.pre or node.body.concludes.pre != c.pre:
            fails.add("eqelim.pre", where, "premise pre mismatch")
        want_eq = (FAtom("=", node.termU, node.termT) if node.flipped
                   else FAtom("=", node.termT, node.termU))
        if node.eq.concludes.post != want_eq:
            fails.add("eqelim.eq-form", where,
                      f"eq premise post != {'(u = t)' if node.flipped else '(t = u)'}")
        if node.body.concludes.post != formula_subst(node.bodyForm, node.wire, node.termT):
            fails.add("eqelim.body-sub", where, "body post != bodyForm[wire := termT]")
        if c.post != formula_subst(node.bodyForm, node.wire, node.termU):
            fails.add("eqelim.concl-sub", where, "conclusion post != bodyForm[wire := termU]")
        return

    if isinstance(node, (PConvIntro, PConvElim)):
        check_proof(node.premise, wire_names, fails, where + ".premise")
        if node.premise.concludes.pre != c.pre:
            fails.add("conv.pre", where, "premise pre mismatch")
        if not node.S < set(range(node.simplex.n + 1)):
            fails.add("conv.S-improper", where, "S must be a PROPER subset")
            return
        try:
            hs = barycentric_halfspace_form(node.term, node.simplex, node.S)
        except ValueError as e:
            fails.add("conv.simplex-degenerate", where, str(e))
            return
        region = FInRegion(node.term, node.simplex, node.S)
        if isinstance(node, PConvIntro):
            if node.premise.concludes.post != hs:
                fails.add("convintro.halfspace", where,
                          "premise post != canonical barycentric halfspace form")
            if c.post != region:
                fails.add("convintro.post", where, "post != region atom")
        else:
            if node.premise.concludes.post != region:
                fails.add("convelim.premise", where, "premise post != region atom")
            if c.post != hs:
                fails.add("convelim.post", where,
                          "post != canonical barycentric halfspace form")
        return

    if isinstance(node, PBernCone):
        check_proof(node.regionProof, wire_names, fails, where + ".region")
        if node.regionProof.concludes.pre != c.pre:
            fails.add("berncone.pre", where, "region premise pre mismatch")
        if node.regionProof.concludes.post != FInRegion(node.termX, node.simplex, node.S):
            fails.add("berncone.region-post", where,
                      "region premise post != FInRegion(termX, simplex, S)")
        if not node.S < set(range(node.simplex.n + 1)):
            fails.add("berncone.S-improper", where, "S must be a PROPER subset")
            return
        # predicate shape (geolog ax/applicable/PBernCone/predicate_*)
        if node.S:
            if not is_conic_predicate(node.predicate):
                fails.add("berncone.predicate-conic", where,
                          "S nonempty requires a conic predicate")
                return
        elif not is_convex_predicate(node.predicate):
            fails.add("berncone.predicate-convex", where,
                      "S empty requires a convex predicate")
            return
        # polynomial scoping (B7 polyTie + the G1 multivariate bridge):
        # the region argument is a wire; over a 1-dim region the polynomial
        # is univariate in that wire (the v0 form); over an n>1-dim region
        # the region wire is rank-1 and every occurrence in the polynomial
        # must be TIdx-indexed with index < n (Term.idx, ruling G1
        # 2026-07-16 — 'scalar component i of a rank-1 term').
        if not isinstance(node.termX, TVar):
            fails.add("berncone.termX", where, "region argument must be a wire")
            return
        if isinstance(node.polynomial, TPoly):
            _check_berncone_poly_payload(node, c, fails, where)
            return
        if isinstance(node.polynomial, TEinsum):
            fails.add("berncone.poly-form", where,
                      "einsum roots are rejected at certificate-payload "
                      "positions (BINARY.md §6.2 terms-v1 discipline)")
            return
        pw = term_free_wires(node.polynomial)
        if not pw <= {node.termX.wire}:
            fails.add("berncone.poly-scope", where,
                      f"polynomial mentions wires {sorted(pw - {node.termX.wire})} "
                      "other than the region argument")
            return
        ndim = node.simplex.n
        try:
            bare, idxd = term_idx_profile(node.polynomial)
        except TypeError as e:
            fails.add("berncone.idx-form", where, str(e))
            return
        sym = {}
        pexpr = term_to_sympy(node.polynomial, sym)
        if ndim == 1:
            if idxd:
                fails.add("berncone.idx-on-1d", where,
                          "TIdx coordinates over a 1-dim region (use the wire)")
                return
            xs = (sym.get(node.termX.wire, sp.Symbol(node.termX.wire)),)
        else:
            if bare:
                fails.add("berncone.bare-wire-ndim", where,
                          f"bare wire occurrence(s) {sorted(bare)} over an "
                          f"{ndim}-dim region (G1: coordinates via TIdx only)")
                return
            if any(i < 0 or i >= ndim for (_, i) in idxd):
                fails.add("berncone.idx-range", where,
                          f"TIdx index out of range for ambient dim {ndim}")
                return
            xs = tuple(sym.get(idx_symbol_name(node.termX.wire, i),
                               sp.Symbol(idx_symbol_name(node.termX.wire, i)))
                       for i in range(ndim))
        # the (j, gamma) coefficient grid, recomputed exactly
        # (geolog allForwardDiffBernCoeffsSatisfyP recomputes from ground data)
        try:
            b = bernstein_coeffs(pexpr, xs, node.simplex.vertices, node.degree)
        except ValueError as e:
            cid = "berncone.degree" if "exceeds" in str(e) else "berncone.compute"
            fails.add(cid, where, str(e))
            return
        grid = berncone_grid(b, node.degree, tuple(sorted(node.S)))
        flat = []
        for j, fam in sorted(grid.items()):
            for gamma, val in sorted(fam.items()):
                flat.append((j, gamma, sp.Rational(val)))
                inst = apply_predicate(node.predicate, TConst(sp.Rational(val)))
                if not eval_ground_formula(inst):
                    fails.add("berncone.coeff", where,
                              f"coefficient P_{j}[{gamma}] = {val} violates predicate")
        if node.stored_grid and tuple(flat) != tuple(node.stored_grid):
            fails.add("berncone.stored-grid", where,
                      "stored coefficient grid != recomputed grid")
        # conclusion form (geolog applyPredicateToTerm)
        if c.post != apply_predicate(node.predicate, node.polynomial):
            fails.add("berncone.post", where,
                      "post != predicate applied to the polynomial term")
        return

    if isinstance(node, PIntMono):
        # jet-v1 [J3] (contract §3): pointwise-cone => integral row.
        # The one sequent-fragment addition — PSyzygy consumes the
        # conclusion natively; soundness is rung lemma L3 under the
        # box-confinement hypotheses carried in pre.
        if not isinstance(node.premise.concludes, Judgment):
            fails.add("intmono.premise-kind", where,
                      "premise must conclude a sequent judgment "
                      "(jet judgments are never premises in jet-v1)")
            return
        check_proof(node.premise, wire_names, fails, where + ".premise")
        if not check_jet_frame(node.frame, wire_names, fails, where):
            return
        if node.premise.concludes.pre != c.pre:
            fails.add("intmono.pre", where, "premise pre != conclusion pre")
        if node.int_wire == HOLE or node.int_wire not in wire_names:
            fails.add("intmono.intwire", where,
                      f"integral wire {node.int_wire!r} is not a declared wire")
            return
        if node.int_wire in node.frame.wires:
            fails.add("intmono.intwire", where,
                      "an integral wire is never a jet wire ([J3b])")
        h_link = _linkage_hypernet()
        if h_link is not None:
            dt = {w.name: w.dtype for w in h_link.wires}
            if dt.get(node.int_wire) not in (None, "Q"):
                fails.add("intmono.intwire", where,
                          f"integral wire must be exact-Q, got "
                          f"{dt[node.int_wire]!r}")
        if not _jet_tree_fragment(node.integrand):
            # jet-v1 review r1 SF-2: the staged polynomialCanonicalEq
            # realization (PNorm) is index-free-tree-only; the integrand
            # fragment gate keeps rule and axioms on one term domain
            # (the family-v1 drift-fragment-gate pattern).
            fails.add("intmono.integrand-fragment", where,
                      "integrand must be an index-free tree term "
                      "(const/var/add/mul/sub)")
            return
        q = _jet_dict(node.integrand, node.frame, fails,
                      where + ".integrand", "intmono.scope")
        if q is None:
            return
        pj = node.premise.concludes.post
        if not (isinstance(pj, FAtom) and pj.op == "<="
                and pj.r == TConst(Rational(0))):
            fails.add("intmono.premise-shape", where,
                      "premise post is not (l <= 0)")
            return
        try:
            l_expr = sp.expand(term_to_sympy(pj.l, {}))
            q_expr = sp.expand(term_to_sympy(node.integrand, {}))
        except (TypeError, ValueError) as e:
            fails.add("intmono.premise-shape", where, str(e))
            return
        if sp.expand(l_expr + q_expr) != 0:
            fails.add("intmono.premise-poly", where,
                      "premise LHS != -(integrand) as polynomials "
                      "(the value-exact arm)")
        post = c.post
        if not (isinstance(post, FAtom) and post.op == "<="
                and post.r == TConst(Rational(0))):
            fails.add("intmono.post", where, "conclusion post is not (l <= 0)")
            return
        try:
            l2_expr = sp.expand(term_to_sympy(post.l, {}))
        except (TypeError, ValueError) as e:
            fails.add("intmono.post", where, str(e))
            return
        if sp.expand(l2_expr + sp.Symbol(node.int_wire)) != 0:
            fails.add("intmono.post", where,
                      "conclusion LHS != -(integral wire) value-exactly")
        return

    if isinstance(node, PFarkas):
        if len(node.premises) != len(node.lambdas):
            fails.add("farkas.arity", where, "premise/lambda count mismatch")
            return
        combo = sp.Integer(0)
        sym = {}
        for i, prem in enumerate(node.premises):
            check_proof(prem, wire_names, fails, where + f".premise[{i}]")
            if prem.concludes.pre != c.pre:
                fails.add("farkas.pre", where, f"premise[{i}] pre mismatch")
            pj = prem.concludes.post
            if not (isinstance(pj, FAtom) and pj.op == "<=" and pj.r == TConst(Rational(0))):
                fails.add("farkas.premise-shape", where,
                          f"premise[{i}] post is not (t <= 0)")
                continue
            lam = sp.Rational(node.lambdas[i])
            if lam < 0:
                fails.add("farkas.lambda-negative", where, f"lambda[{i}] = {lam} < 0")
            combo += lam * term_to_sympy(pj.l, sym)
        # TIdx-aware canonical reconstruction (G1): coordinate symbols map
        # back to TIdx terms so the emitter's conclusion AST is comparable.
        # Accept EITHER the canonical AST (the v0 emission convention;
        # projective — canon rescales to primitive-integer form, sound
        # for <=0 atoms) OR value-exact polynomial equality with the
        # combination — the Lean contract (`farkasCheck`: fold ==
        # conclusion.toPoly, exact; the wire emitter's syzygy-scale
        # shortcut has always targeted this).  X2 producers use the
        # value-exact arm to conclude literal-shaped atoms.
        want = canon_term(combo, wire_of_sym_from(sym, wire_names))
        if node.conclusion != want:
            cdiff = sp.expand(term_to_sympy(node.conclusion, sym) - combo)
            if cdiff != 0:
                fails.add("farkas.combination", where,
                          "conclusion is neither the canon AST nor "
                          "value-exact against the combination")
        if c.post != FAtom("<=", node.conclusion, TConst(Rational(0))):
            fails.add("farkas.post", where, "post != (conclusion <= 0)")
        return

    if isinstance(node, PPromise):
        # CORE rule (AG layer; Lean Soundness `PromiseStep` +
        # `sound_promise`; wire tag 25).  The interface-promise cut,
        # ctx-style: supplier proves the contract; the contract sits as a
        # conjunct of the consumer's pre at `path`; the composite's pre is
        # the consumer's pre with that conjunct replaced by the supplier's
        # pre.  The two confinement side-conditions are CHECKED but never
        # consumed by soundness (the locality warrant — Composition.lean
        # header: "a Promise node without them is just a cut wearing a
        # costume").  Field-for-field the Lean `PromiseStep` obligations.
        check_proof(node.supplier, wire_names, fails, where + ".supplier")
        check_proof(node.consumer, wire_names, fails, where + ".consumer")
        if node.supplier.concludes.post != node.contract:
            fails.add("promise.supplier-post", where,
                      "supplier post != contract")
        try:
            got = conj_get(node.consumer.concludes.pre, node.path)
        except KeyError as e:
            fails.add("promise.path", where, str(e))
            return
        if got != node.contract:
            fails.add("promise.path-reads", where,
                      "consumer pre at path != contract")
        if c.pre != conj_replace(node.consumer.concludes.pre, node.path,
                                 node.supplier.concludes.pre):
            fails.add("promise.pre-plumb", where,
                      "conclusion pre != consumer pre[path := supplier pre]")
        if c.post != node.consumer.concludes.post:
            fails.add("promise.post", where,
                      "conclusion post != consumer post")
        iface = set(node.iface)
        if not formula_free_wires(node.contract) <= iface:
            fails.add("promise.contract-confined", where,
                      f"contract wires {sorted(formula_free_wires(node.contract) - iface)} "
                      "outside the declared interface")
        ctx = conj_replace(node.consumer.concludes.pre, node.path, FTrue())
        shared = formula_free_wires(node.supplier.concludes.pre) & (
            formula_free_wires(ctx) | formula_free_wires(c.post))
        if not shared <= iface:
            fails.add("promise.separation", where,
                      f"supplier-pre wires {sorted(shared - iface)} shared "
                      "with the context or conclusion outside the interface")
        return

    if isinstance(node, PSyzygy):
        # CORE rule (AG layer; Lean Catalogue `syzygyCheck` +
        # Soundness `sound_syzygy`; wire tag 26).  PFarkas's shape lifted
        # two ways: entries range over COMPONENT conclusions (sub-proofs,
        # own premises under premiseContains) and — dialect D's wiring —
        # equality atoms, whose weights carry free sign (realized on the
        # wire as nonneg weights on either polarity; the python model
        # holds the signed weight and emission splits the polarity).
        if len(node.components) != len(node.lambdas):
            fails.add("syzygy.arity", where, "component/lambda count mismatch")
            return
        combo = sp.Integer(0)
        sym = {}
        for i, comp in enumerate(node.components):
            check_proof(comp, wire_names, fails, where + f".component[{i}]")
            if not premise_contains(c.pre, comp.concludes.pre):
                fails.add("syzygy.premise-contains", where,
                          f"component[{i}] pre is not a sub-conjunction of "
                          "the composite pre")
            pj = comp.concludes.post
            lam = sp.Rational(node.lambdas[i])
            if isinstance(pj, FAtom) and pj.op == "=":
                # free-sign wiring entry: lam * (l - r), any sign
                combo += lam * (term_to_sympy(pj.l, sym)
                                - term_to_sympy(pj.r, sym))
                continue
            # X2 widening toward the Lean contract (`atomLeZeroPolys`,
            # Core/Catalogue.lean): every comparison atom enters at its
            # <=0-normal-form polynomial — le/lt as (l - r), ge/gt as
            # (r - l).  Strict premises soundly weaken into the nonstrict
            # conclusion.  The former (t <= 0)-only gate is the r = 0
            # special case of the le arm; X1 certificates are unchanged.
            if not isinstance(pj, FAtom):
                fails.add("syzygy.component-shape", where,
                          f"component[{i}] post is not an atom")
                continue
            if pj.op in ("<=", "<"):
                poly = term_to_sympy(pj.l, sym) - term_to_sympy(pj.r, sym)
            elif pj.op in (">=", ">"):
                poly = term_to_sympy(pj.r, sym) - term_to_sympy(pj.l, sym)
            else:
                fails.add("syzygy.component-shape", where,
                          f"component[{i}] post has op {pj.op!r} — not a "
                          "combination-bearing atom")
                continue
            if lam < 0:
                fails.add("syzygy.lambda-negative", where,
                          f"lambda[{i}] = {lam} < 0 on a non-equality entry")
            combo += lam * poly
        want = canon_term(combo, wire_of_sym_from(sym, wire_names))
        if node.conclusion != want:
            # value-exact arm (the Lean `syzygyCheck` contract; see the
            # PFarkas twin above for the rationale)
            cdiff = sp.expand(term_to_sympy(node.conclusion, sym) - combo)
            if cdiff != 0:
                fails.add("syzygy.combination", where,
                          "conclusion is neither the canon AST nor "
                          "value-exact against the combination")
        if not syzygy_conclusion_form(node.conclusion, c.post):
            fails.add("syzygy.post", where,
                      "post is none of the syzygyConclusionForm readings "
                      "(zero-form / ge-flip / literal) of the conclusion")
        if node.theta is not None:
            th = sp.Rational(node.theta)
            if not (0 < th < 1):
                fails.add("syzygy.theta-range", where,
                          f"theta = {th} outside (0, 1) — the small-gain "
                          "guard modulus range (well-formedness, not "
                          "soundness; BINARY.md sec 2)")
        return

    # ---- X2 batch: arithAtom + norm + the five ReLU/LiRPA rules + unfold --

    if isinstance(node, PArithAtom):
        check_proof(node.premise, wire_names, fails, where + ".premise")
        if node.op not in ("<=", "<", "=", ">=", ">"):
            fails.add("arith.op", where, f"op {node.op!r} not a bowtie "
                      "(ne is excluded — Lean notNE)")
            return
        if node.variant not in ("fold", "unfold"):
            fails.add("arith.variant", where, f"variant {node.variant!r}")
            return
        if node.premise.concludes.pre != c.pre:
            fails.add("arith.pre", where, "premise pre mismatch")
        zero = FAtom(node.op, TSub(node.termL, node.termR),
                     TConst(Rational(0)))
        direct = FAtom(node.op, node.termL, node.termR)
        if node.variant == "fold":
            if node.premise.concludes.post != zero:
                fails.add("arith.fold-premise", where,
                          "premise post != ((l - r) op 0)")
            if c.post != direct:
                fails.add("arith.fold-post", where, "post != (l op r)")
        else:
            if node.premise.concludes.post != direct:
                fails.add("arith.unfold-premise", where,
                          "premise post != (l op r)")
            if c.post != zero:
                fails.add("arith.unfold-post", where,
                          "post != ((l - r) op 0)")
        return

    if isinstance(node, PConstExact):
        # constExact (TIER-2 ADMISSIBLE, Lean PConstExactData; no wire
        # tag — v1 payload window).  Premise-free; post = (e1 op e2)
        # for CLOSED terms; op != '!=' (notNE); the ground comparison
        # must HOLD — Lean `(Formula.atom b e1 e2).evalClosed = some
        # true` (evalQ? succeeds iff wire-free; the python mirror
        # evaluates in sympy and requires no free symbols).
        if node.op not in ("<=", "<", "=", ">=", ">"):
            fails.add("constexact.op", where, f"op {node.op!r} not a "
                      "bowtie (ne is excluded — Lean notNE)")
            return
        sym = {}
        v1 = term_to_sympy(node.e1, sym)
        v2 = term_to_sympy(node.e2, sym)
        if sym:
            fails.add("constexact.closed", where,
                      f"terms are not wire-free (free: {sorted(sym)})")
            return
        holds = {"<=": v1 <= v2, "<": v1 < v2, "=": v1 == v2,
                 ">=": v1 >= v2, ">": v1 > v2}[node.op]
        if not holds:
            fails.add("constexact.holds", where,
                      f"ground comparison ({v1} {node.op} {v2}) is FALSE")
        if c.post != FAtom(node.op, node.e1, node.e2):
            fails.add("constexact.post", where, "post != (e1 op e2)")
        return

    if isinstance(node, PNorm):
        # Lean polynomialCanonicalEq: idx-free both sides + toPoly
        # equality (VALUE-preserving — nothing rescales; canon_sympy's
        # primitive-integer rescale is deliberately NOT used here).
        def _idx_free(t):
            if isinstance(t, (TConst, TVar)):
                return True
            if isinstance(t, (TAdd, TMul, TSub)):
                return _idx_free(t.l) and _idx_free(t.r)
            return False
        if not (_idx_free(node.termL) and _idx_free(node.termR)):
            fails.add("norm.idx-free", where,
                      "both sides must be idx-free polynomial terms "
                      "(TConst/TVar/TAdd/TMul/TSub)")
            return
        sym = {}
        diff = sp.expand(term_to_sympy(node.termL, sym)
                         - term_to_sympy(node.termR, sym))
        if diff != 0:
            fails.add("norm.canon", where,
                      "termL and termR differ as Q-polynomials")
        if c.post != FAtom("=", node.termL, node.termR):
            fails.add("norm.post", where, "post != (termL = termR)")
        return

    if isinstance(node, PLiRPA):
        check_proof(node.lower, wire_names, fails, where + ".lower")
        check_proof(node.upper, wire_names, fails, where + ".upper")
        if not _linkage_check(node.preact, node.post, fails, where,
                              "lirpa"):
            return
        a, b = sp.Rational(node.a), sp.Rational(node.b)
        al, be = sp.Rational(node.alpha), sp.Rational(node.beta)
        ga, de = sp.Rational(node.gamma), sp.Rational(node.delta)
        if not a < 0:
            fails.add("lirpa.a-neg", where, f"a = {a} not < 0")
        if not b > 0:
            fails.add("lirpa.b-pos", where, f"b = {b} not > 0")
        # the six envelope side conditions (Lean hLower1-3, hUpper1-3)
        if not al * a + be <= 0:
            fails.add("lirpa.lower1", where, "alpha*a + beta > 0")
        if not be <= 0:
            fails.add("lirpa.lower2", where, "beta > 0")
        if not al * b + be <= b:
            fails.add("lirpa.lower3", where, "alpha*b + beta > b")
        if not ga * a + de >= 0:
            fails.add("lirpa.upper1", where, "gamma*a + delta < 0")
        if not de >= 0:
            fails.add("lirpa.upper2", where, "delta < 0")
        if not ga * b + de >= b:
            fails.add("lirpa.upper3", where, "gamma*b + delta < b")
        if node.lower.concludes.pre != c.pre:
            fails.add("lirpa.pre", where, "lower premise pre mismatch")
        if node.upper.concludes.pre != node.lower.concludes.pre:
            fails.add("lirpa.pre-match", where,
                      "upper premise pre != lower premise pre")
        if node.lower.concludes.post != FAtom(
                "<=", TConst(Rational(a)), TVar(node.preact)):
            fails.add("lirpa.lower-post", where,
                      "lower premise post != (a <= preact)")
        if node.upper.concludes.post != FAtom(
                "<=", TVar(node.preact), TConst(Rational(b))):
            fails.add("lirpa.upper-post", where,
                      "upper premise post != (preact <= b)")
        # lirpaConclusionForm: pinned affineWireTerm ASTs
        lo_t = TAdd(TConst(Rational(be)),
                    TMul(TConst(Rational(al)), TVar(node.preact)))
        hi_t = TAdd(TConst(Rational(de)),
                    TMul(TConst(Rational(ga)), TVar(node.preact)))
        want = FAnd(FAtom("<=", lo_t, TVar(node.post)),
                    FAtom("<=", TVar(node.post), hi_t))
        if c.post != want:
            fails.add("lirpa.post", where,
                      "post != lirpaConclusionForm sandwich")
        return

    if isinstance(node, PReLUPos):
        check_proof(node.premise, wire_names, fails, where + ".premise")
        if not _linkage_check(node.preact, node.post, fails, where,
                              "relupos"):
            return
        if node.premise.concludes.pre != c.pre:
            fails.add("relupos.pre", where, "premise pre mismatch")
        if node.premise.concludes.post != FAtom(
                ">=", TVar(node.preact), TConst(Rational(0))):
            fails.add("relupos.premise-post", where,
                      "premise post != (preact >= 0)")
        if c.post != FAtom("=", TVar(node.post), TVar(node.preact)):
            fails.add("relupos.post", where, "post != (post = preact)")
        return

    if isinstance(node, PReLUNeg):
        check_proof(node.premise, wire_names, fails, where + ".premise")
        if not _linkage_check(node.preact, node.post, fails, where,
                              "reluneg"):
            return
        if node.premise.concludes.pre != c.pre:
            fails.add("reluneg.pre", where, "premise pre mismatch")
        if node.premise.concludes.post != FAtom(
                "<=", TVar(node.preact), TConst(Rational(0))):
            fails.add("reluneg.premise-post", where,
                      "premise post != (preact <= 0)")
        if c.post != FAtom("=", TVar(node.post), TConst(Rational(0))):
            fails.add("reluneg.post", where, "post != (post = 0)")
        return

    if isinstance(node, PReLUNN):
        if not _linkage_check(node.preact, node.post, fails, where,
                              "relunn"):
            return
        if c.post != FAtom(">=", TVar(node.post), TConst(Rational(0))):
            fails.add("relunn.post", where, "post != (post >= 0)")
        return

    if isinstance(node, PReLUAbove):
        if not _linkage_check(node.preact, node.post, fails, where,
                              "reluabove"):
            return
        if c.post != FAtom(">=", TVar(node.post), TVar(node.preact)):
            fails.add("reluabove.post", where, "post != (post >= preact)")
        return

    if isinstance(node, PReluUnfold):
        if not ALLOW_UNSTAGED_UNFOLD:
            fails.add("unfold.unstaged", where,
                      "PReluUnfold has no staged Lean constructor / wire "
                      "tag yet (Obligation U's rule realization rides "
                      "ahead of its mechanization); set "
                      "bl_checker.ALLOW_UNSTAGED_UNFOLD for experiments")
            return
        if not _linkage_check(node.preact, node.post, fails, where,
                              "unfold"):
            return
        fresh = node.fresh
        if len(fresh) != RELU_UNFOLD_ARITY or len(set(fresh)) != len(fresh):
            fails.add("unfold.fresh-arity", where,
                      f"fresh must be {RELU_UNFOLD_ARITY} distinct names")
            return
        import re as _re
        if any(_re.fullmatch(r".*__\d+", f) for f in fresh):
            fails.add("unfold.fresh-reserved", where,
                      "fresh wires must avoid the reserved <base>__<digits> "
                      "coordinate namespace (wf.reserved-name's twin)")
            return
        clash = set(fresh) & wire_names
        if clash:
            fails.add("unfold.fresh-clash", where,
                      f"fresh wires already exist: {sorted(clash)}")
            return
        used = formula_free_wires(c.pre) | formula_free_wires(c.post)
        if set(fresh) & used:
            fails.add("unfold.fresh-in-sequent", where,
                      "fresh wires occur free in the conclusion sequent")
            return
        exp = relu_expansion_spfacts(node.preact, node.post, fresh)
        if node.premise.concludes.pre != FAnd(c.pre, exp):
            fails.add("unfold.premise-pre", where,
                      "premise pre != And(pre, recomputed expansion "
                      "sp-facts)")
        if node.premise.concludes.post != c.post:
            fails.add("unfold.premise-post", where,
                      "premise post != conclusion post")
        check_proof(node.premise, wire_names | set(fresh), fails,
                    where + ".premise")
        return

    fails.add("unknown-rule", where, type(node).__name__)


# =========================================================================
# top-level certificate check
# =========================================================================

def check_certificate(hypernet: Hypernet, vc_hyp: Formula, vc_post: Formula,
                      root: Proof) -> Failures:
    """Full check: hypernet wf + SP_H synthesis-and-compare (B4) + root
    sequent identity + recursive proof check.  Empty list <=> ACCEPT."""
    fails = Failures()
    check_hypernet(hypernet, fails)

    if isinstance(root, (PProductLattice, PEnclosure, PJetDiv,
                         PFunctionalDeriv)):
        # judgement-kind roots (famJudgment / encJudgment / jet
        # judgements): the file's user-facing goal IS the root's
        # judgement; no Phi/sph decomposition applies (BINARY.md SS6.3;
        # jet-v1 contract SS3 root-only profile), so the sequent
        # identity checks are vacuous here — the rule's own clause in
        # check_proof carries the whole obligation.
        pass
    else:
        expected_pre = FAnd(vc_hyp, sp_H(hypernet))
        if root.concludes.pre != expected_pre:
            fails.add("root.pre", "root",
                      "root pre != (VC hypothesis AND synthesized SP_H) — "
                      "sp-facts are verified against the hypernet, never "
                      "trusted (B4)")
        if root.concludes.post != vc_post:
            fails.add("root.post", "root", "root post != VC conclusion")

    wire_names = {w.name for w in hypernet.wires} | {HOLE}
    set_linkage_hypernet(hypernet)
    try:
        check_proof(root, wire_names, fails)
        check_jet_bindings(root, fails)   # [J4], certificate-global
    finally:
        set_linkage_hypernet(None)
    return fails


# ---------------------------------------------------------------------------
# terms-v1: the BernCone poly-record payload path (BINARY.md §6.2)
# ---------------------------------------------------------------------------

def _check_berncone_poly_payload(node, c, fails, where):
    """The §6.2 terms-v1 payload discipline: aboutness pinned as manifest
    data (B7 dissolved), fast path when the frame matches the node, the
    checked basis-conversion path otherwise. Both paths land in the same
    recomputed (j, gamma) grid + predicate loop as the tree path — R15's
    recompute-normative arm untouched."""
    import sympy as sp
    from bl_bernstein import bernstein_coeffs, berncone_grid, multi_indices

    P = node.polynomial
    wf = tpoly_wf_errors(P)
    if wf:
        fails.add("berncone.poly-wf", where, "; ".join(wf))
        return
    ndim = node.simplex.n
    if ndim == 1:
        want = ((node.termX.wire, None),)
    else:
        want = tuple((node.termX.wire, j) for j in range(ndim))
    if tuple(P.support) != want:
        fails.add("berncone.poly-aboutness", where,
                  f"support {P.support} != the canonical coordinate family "
                  f"of {node.termX.wire} over an {ndim}-dim region")
        return
    sym = {}
    # §6.2 precondition 0: the NODE's simplex passes the exact
    # affine-rank check before any conversion or grid step, both paths.
    xs_probe = [sp.Symbol(f"__nd{i}") for i in range(ndim)]
    try:
        barycentric_exprs(node.simplex.vertices, xs_probe)
    except ValueError as e:
        fails.add("berncone.poly-domain-degenerate", where,
                  f"node simplex: {e}")
        return
    if P.basis == "bernstein" and P.domain != node.simplex:
        # a different source domain gets its own check (§6.1)
        try:
            barycentric_exprs(P.domain.vertices, xs_probe)
        except ValueError as e:
            fails.add("berncone.poly-domain-degenerate", where, str(e))
            return
    if (P.basis == "bernstein" and P.domain == node.simplex
            and P.degree == node.degree):
        # FAST PATH: stored coefficients ARE the degree-d Bernstein
        # family; materialize absent indices as exact zeros (the
        # predicate must hold on those too) and skip only the
        # polynomial->Bernstein conversion.
        b = {alpha: sp.Integer(0)
             for alpha in multi_indices(ndim + 1, node.degree)}
        for alpha, coeff in P.entries:
            b[tuple(alpha)] = sp.Rational(coeff)
    else:
        # GENERAL PATH: expand through the §6.1 evaluation semantics
        # (explicit checked basis conversion) into the tree path's
        # kernel.
        try:
            pexpr = tpoly_to_sympy(P, sym)
        except (ValueError, TypeError) as e:
            fails.add("berncone.poly-expand", where, str(e))
            return
        if ndim == 1:
            xs = (sym.get(node.termX.wire, sp.Symbol(node.termX.wire)),)
        else:
            xs = tuple(sym.get(idx_symbol_name(node.termX.wire, i),
                               sp.Symbol(idx_symbol_name(node.termX.wire, i)))
                       for i in range(ndim))
        try:
            b = bernstein_coeffs(pexpr, xs, node.simplex.vertices,
                                 node.degree)
        except ValueError as e:
            cid = ("berncone.degree" if "exceeds" in str(e)
                   else "berncone.compute")
            fails.add(cid, where, str(e))
            return
    grid = berncone_grid(b, node.degree, tuple(sorted(node.S)))
    flat = []
    for j, fam in sorted(grid.items()):
        for gamma, val in sorted(fam.items()):
            flat.append((j, gamma, sp.Rational(val)))
            inst = apply_predicate(node.predicate, TConst(sp.Rational(val)))
            if not eval_ground_formula(inst):
                fails.add("berncone.coeff", where,
                          f"coefficient P_{j}[{gamma}] = {val} violates "
                          "predicate")
    if node.stored_grid and tuple(flat) != tuple(node.stored_grid):
        fails.add("berncone.stored-grid", where,
                  "stored coefficient grid != recomputed grid")
    if c.post != apply_predicate(node.predicate, node.polynomial):
        fails.add("berncone.post", where,
                  "post != predicate applied to the polynomial term")


# =========================================================================
# family-v1 (2026-07-17): blocklattice / productLattice checks
# BINARY.md SS6.1 [F1]/[F2] + SS6.2 [F3]/[F4]/[F5]. The facet-proof
# NODES are checked by the ordinary tag-11 machinery (check_proof);
# the family layer adds only combinatorics + conclusion-shape checks.
# =========================================================================

def _f2_extract_atoms(f: Formula, fails, where):
    """Walk an [F2] pre AND-tree; return {wire: (lo, hi)} from
    FInRegion(TVar(w), 1-simplex, {}) atoms, or None on shape failure."""
    out = {}

    def walk(g):
        if isinstance(g, FAnd):
            return walk(g.l) and walk(g.r)
        if isinstance(g, FInRegion):
            if not isinstance(g.term, TVar) or g.term.wire == HOLE:
                fails.add("fam.f2.pre-atom", where,
                          f"pre atom region argument must be a real wire: {g!r}")
                return False
            if g.S:
                fails.add("fam.f2.pre-atom", where,
                          "pre atom extension set must be empty")
                return False
            vs = g.simplex.vertices
            if len(vs) != 2 or len(vs[0]) != 1 or len(vs[1]) != 1:
                fails.add("fam.f2.pre-atom", where,
                          f"pre atom region must be a 1-simplex: {g.simplex!r}")
                return False
            lo, hi = vs[0][0], vs[1][0]
            if not lo < hi:
                fails.add("fam.f2.pre-atom", where,
                          f"pre atom interval degenerate: [{lo}, {hi}]")
                return False
            w = g.term.wire
            if w in out:
                fails.add("fam.f2.pre-atom", where,
                          f"two pre atoms over one wire {w}")
                return False
            out[w] = (lo, hi)
            return True
        fails.add("fam.f2.pre-shape", where,
                  f"pre must be an AND-tree of inRegion atoms; found {g!r}")
        return False

    return out if walk(f) else None


def _f2_check_facet(L: BlockLattice, block: FamBlock, k: int, facet,
                    proof: Proof, fails, where):
    """[F2] conclusion-shape check for facet k of a block (BINARY.md SS6.1
    rules 1-4). The node itself is checked by check_proof at the caller."""
    idx, axis, d = facet
    co = L.cell_coords(idx)
    v = L.facet_pinned_value(facet)
    wires = [w for (w, _, _) in L.axes]
    w_pinned = wires[axis]
    drift = L.axes[axis][1]
    c = proof.concludes
    if not isinstance(c, Judgment):
        fails.add("fam.f2.concludes", where,
                  f"facet {k} proof concludes a non-sequent judgment")
        return
    # rule 1: post shape + orientation
    post = c.post
    if not (isinstance(post, FAtom) and isinstance(post.r, TConst)
            and post.op in (">=", "<=")):
        fails.add("fam.f2.post", where,
                  f"facet {k}: post must be FAtom(>=|<=, P, const)")
        return
    m = post.r.value
    if d == -1 and not (post.op == ">=" and m > 0):
        fails.add("fam.f2.orientation", where,
                  f"facet {k}: lower face (block on + side) needs "
                  f">= with positive margin, got {post.op} {m}")
    if d == 1 and not (post.op == "<=" and m < 0):
        fails.add("fam.f2.orientation", where,
                  f"facet {k}: upper face (block on - side) needs "
                  f"<= with negative margin, got {post.op} {m}")
    # rule 2: polynomial = pinned-substituted drift (structural tree eq)
    want_poly = subst_tree(drift, w_pinned, v)
    if post.l != want_poly:
        fails.add("fam.f2.polynomial", where,
                  f"facet {k}: polynomial != drift[{w_pinned} := {v}] "
                  "(pure tree substitution)")
    # rule 3: pre atoms
    atoms = _f2_extract_atoms(c.pre, fails, where + f".facet{k}")
    if atoms is None:
        return
    free_axes = [j for j in range(L.amb_dim) if j != axis]
    for w, (lo, hi) in atoms.items():
        if w not in wires:
            fails.add("fam.f2.scope", where,
                      f"facet {k}: pre atom over foreign wire {w}")
            continue
        j = wires.index(w)
        if j in free_axes:
            want = L.cell_interval(co, j)
            if (lo, hi) != want:
                fails.add("fam.f2.free-interval", where,
                          f"facet {k}: free-axis atom [{lo},{hi}] != cell "
                          f"interval [{want[0]},{want[1]}]")
        else:
            want = L.arena_interval(j)
            if (lo, hi) != want:
                fails.add("fam.f2.idle-interval", where,
                          f"facet {k}: non-free-axis atom [{lo},{hi}] != "
                          f"full arena [{want[0]},{want[1]}]")
    # rule 4: scope of the whole conclusion
    extra = (formula_free_wires(c.pre) | formula_free_wires(c.post)) \
        - set(wires) - {HOLE}
    if extra:
        fails.add("fam.f2.scope", where,
                  f"facet {k}: conclusion mentions foreign wires "
                  f"{sorted(extra)}")


def check_blocklattice(L: BlockLattice, fails, where="lattice",
                       check_nodes=True):
    """[F1] record-level well-formedness + [F2] per-facet discharge.
    With check_nodes, every facet proof node also runs through
    check_proof (the tag-11 machinery — grid recompute)."""
    # [F1] axes
    wires = [w for (w, _, _) in L.axes]
    if not 1 <= L.amb_dim <= 2:
        fails.add("fam.f1.amb-dim", where,
                  f"amb_dim {L.amb_dim} outside the family-v1 gate")
        return
    if len(set(wires)) != len(wires):
        fails.add("fam.f1.axis-wires", where, "duplicate axis wires")
        return
    for i, (w, drift, g) in enumerate(L.axes):
        if len(g) < 2 or any(not g[k] < g[k + 1] for k in range(len(g) - 1)):
            fails.add("fam.f1.gridlines", where,
                      f"axis {i}: gridlines must be >= 2, strictly "
                      "increasing")
            return
        leak = term_free_wires(drift) - set(wires)
        if leak:
            fails.add("fam.f3.confinement", where,
                      f"axis {i} drift mentions non-axis wires "
                      f"{sorted(leak)}")

        def _frag_ok(t):
            if isinstance(t, TVar):
                return t.wire != HOLE
            if isinstance(t, TConst):
                return True
            if isinstance(t, (FAnd,)):
                return False
            from bl_cert import TAdd, TMul, TSub
            if isinstance(t, (TAdd, TMul, TSub)):
                return _frag_ok(t.l) and _frag_ok(t.r)
            return False
        if not _frag_ok(drift):
            fails.add("fam.f1.drift-fragment", where,
                      f"axis {i} drift outside the scalar tree fragment "
                      "(F-A5)")
    # [F1] blocks
    seen = set()
    n = L.n_cells
    if not L.blocks:
        fails.add("fam.f1.blocks", where, "n_blocks must be >= 1")
        return
    for bi, b in enumerate(L.blocks):
        if not b.cells or not b.cells < frozenset(range(n)):
            fails.add("fam.f1.block-cells", where,
                      f"block {bi}: must be a nonempty PROPER subset of "
                      f"the {n} cells")
            return
        if b.cells in seen:
            fails.add("fam.f1.block-dup", where, f"block {bi}: duplicate")
            return
        seen.add(b.cells)
        facets = L.boundary_facets(b.cells)
        if len(b.facet_proofs) != len(facets):
            fails.add("fam.f1.facet-count", where,
                      f"block {bi}: {len(b.facet_proofs)} facet proofs != "
                      f"{len(facets)} recomputed boundary facets")
            return
        for k, (facet, proof) in enumerate(zip(facets, b.facet_proofs)):
            if check_nodes:
                check_proof(proof, set(wires) | {HOLE}, fails,
                            f"{where}.b{bi}.f{k}")
            _f2_check_facet(L, b, k, facet, proof, fails,
                            f"{where}.b{bi}")


def check_product_lattice(node: PProductLattice, fails, where="root"):
    """Node tag 27: [F1]/[F2] on all three records + [F3] confinement
    (inside check_blocklattice) + [F4] disjointness + [F5] composite =
    the product construction + concludes integrity."""
    if not isinstance(node.concludes, FamJudgment) \
            or node.concludes.lattice is not node.composite \
            and node.concludes.lattice != node.composite:
        fails.add("fam.concludes", where,
                  "concludes famJudgment must carry the composite record")
    check_blocklattice(node.left, fails, where + ".left")
    check_blocklattice(node.right, fails, where + ".right")
    check_blocklattice(node.composite, fails, where + ".composite")
    # [F4] disjointness
    lw = set(w for (w, _, _) in node.left.axes)
    rw = set(w for (w, _, _) in node.right.axes)
    if lw & rw:
        fails.add("fam.f4.disjoint", where,
                  f"factor axis wires shared: {sorted(lw & rw)}")
        return
    # [F5] composite = product construction, field-for-field
    want_axes = node.left.axes + node.right.axes
    if node.composite.axes != want_axes:
        fails.add("fam.f5.axes", where,
                  "composite axes != left's then right's (wires, drift "
                  "terms, gridlines verbatim)")
        return
    want_blocks = product_lattice_blocks(node.left, node.right)
    got_blocks = tuple(b.cells for b in node.composite.blocks)
    if got_blocks != want_blocks:
        fails.add("fam.f5.blocks", where,
                  f"composite blocks != extended-product enumeration "
                  f"({len(got_blocks)} stored vs {len(want_blocks)} "
                  "expected, or order/content mismatch)")


# ---------------------------------------------------------------------------
# enclosure-v1 (2026-07-17): tag-28 remainder-bound check
# ---------------------------------------------------------------------------
# Lean-twin arithmetic (Enclosure.lean maclaurin/tailBound/encCheck; keep
# in EXACT sync -- producer/enclosure.py is the Fraction twin, this is the
# sympy-Rational twin; producer/test_enclosure.py pins both to the Lean
# kernel receipts).

def enc_maclaurin(func: str, k: int) -> Rational:
    """Exact Maclaurin coefficient a_k of the tagged function."""
    import math
    if func == "exp":
        return Rational(1, math.factorial(k))
    if func == "sin":
        if k % 2 == 1:
            return Rational((-1) ** ((k - 1) // 2), math.factorial(k))
        return Rational(0)
    if func == "cos":
        if k % 2 == 0:
            return Rational((-1) ** (k // 2), math.factorial(k))
        return Rational(0)
    raise ValueError(f"unknown enclosure func {func!r}")


def enc_tail_bound(n: int, r: Rational) -> Rational:
    """r^(n+1)/(n+1)! * (n+2)/(n+2-r); needs 0 <= r < n+2 (checked by
    caller -- [E2] precedes [E3])."""
    import math
    return (Rational(r) ** (n + 1) / math.factorial(n + 1)
            * Rational(n + 2) / (Rational(n + 2) - Rational(r)))


def check_enclosure(node: PEnclosure, fails: Failures, where="root"):
    """Node tag 28: the encCheck side conditions on the node's
    EncJudgment conclusion (BINARY.md SS6.2 [E1]-[E3]). [E1] holds by
    recomputation here (the wire never carries coefficients; this
    model-level checker likewise recomputes -- the recompute pattern);
    [E2] radius guard, [E3] tail cap, both exact. Fail-closed: any
    malformed field is a failure, never a skip."""
    j = node.concludes
    if not isinstance(j, EncJudgment):
        fails.add("enc.concludes", where,
                  "tag-28 node must conclude an EncJudgment (0x32)")
        return
    if j.func not in ENC_FUNCS:
        fails.add("enc.func", where, f"unknown func tag {j.func!r}")
        return
    if not (isinstance(j.n, int) and not isinstance(j.n, bool)
            and j.n >= 0):
        fails.add("enc.n", where, f"degree must be a nonneg int, got {j.n!r}")
        return
    try:
        r, R = Rational(j.r), Rational(j.R)
    except (TypeError, ValueError):
        fails.add("enc.rat", where, "r/R not exact rationals")
        return
    # [E2] radius: 0 <= r < n+2, strict (the geometric-sum guard).
    if not (0 <= r and r < j.n + 2):
        fails.add("enc.radius", where,
                  f"radius {r} outside [0, {j.n + 2}) for n={j.n}")
        return
    # [E1] coefficients: recomputed canonical prefix (by construction
    # equal to the recurrence; kept as an executed step so this clause
    # IS encCheck, not a subset of it).
    coeffs = tuple(enc_maclaurin(j.func, k) for k in range(j.n + 1))
    assert len(coeffs) == j.n + 1
    # [E3] tail cap.
    if not (enc_tail_bound(j.n, r) <= R):
        fails.add("enc.tail", where,
                  f"R = {R} below tail({j.n}, {r}) = "
                  f"{enc_tail_bound(j.n, r)}")


# ---------------------------------------------------------------------------
# jet-v1: the jet-arithmetic kernel + judgement-kind root checks.
# Contract: the upstream jet-v1 revision contract SS3 ([J0]-[J2];
# [J3] is the PIntMono clause in check_proof). The dict-of-multi-indices
# arithmetic is the Fraction-exact form of the two PDE artefacts'
# independently-landed pDx routines (companion experiments repository)
# -- coefficients here are sympy Rationals, keys are TRIMMED exponent
# tuples (no trailing zeros), so dict equality is canonical.
# ---------------------------------------------------------------------------

def _jd_trim(m):
    m = tuple(m)
    while m and m[-1] == 0:
        m = m[:-1]
    return m


def _jd_add(a, b):
    out = dict(a)
    for m, c in b.items():
        v = out.get(m, sp.Integer(0)) + c
        if v == 0:
            out.pop(m, None)
        else:
            out[m] = v
    return out


def _jd_mul(a, b):
    out = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            w = max(len(m1), len(m2))
            m = _jd_trim(tuple((m1[i] if i < len(m1) else 0)
                               + (m2[i] if i < len(m2) else 0)
                               for i in range(w)))
            v = out.get(m, sp.Integer(0)) + c1 * c2
            if v == 0:
                out.pop(m, None)
            else:
                out[m] = v
    return out


def _jd_diff(d, j):
    """d/du_j on a jet dict."""
    out = {}
    for m, c in d.items():
        if j < len(m) and m[j] > 0:
            m2 = list(m)
            m2[j] -= 1
            k = _jd_trim(m2)
            v = out.get(k, sp.Integer(0)) + c * m[j]
            if v == 0:
                out.pop(k, None)
            else:
                out[k] = v
    return out


def _jd_dx(d):
    """The total derivative D_x (D_x u_j = u_{j+1}), width-growing."""
    out = {}
    for m, c in d.items():
        for j in range(len(m)):
            if m[j] > 0:
                m2 = list(m) + [0] * (j + 2 - len(m) if j + 2 > len(m) else 0)
                m2[j] -= 1
                m2[j + 1] += 1
                k = _jd_trim(m2)
                v = out.get(k, sp.Integer(0)) + c * m[j]
                if v == 0:
                    out.pop(k, None)
                else:
                    out[k] = v
    return out


def _jet_dict(t, frame: JetFrame, fails: Failures, where: str, scope_id: str):
    """Evaluate a Term to a jet dict over the frame coordinates (wire
    names = symbols, the term_to_sympy convention). None + a recorded
    failure on scope violations or non-polynomial content."""
    try:
        expr = sp.expand(term_to_sympy(t, {}))
    except (TypeError, ValueError) as e:
        fails.add(scope_id, where, f"term does not evaluate: {e}")
        return None
    extra = {s.name for s in expr.free_symbols} - set(frame.wires)
    if extra:
        fails.add(scope_id, where,
                  f"term mentions non-frame wires {sorted(extra)} "
                  "(jetScoped)")
        return None
    if expr == 0:
        return {}
    xs = [sp.Symbol(w) for w in frame.wires]
    p = sp.Poly(expr, *xs)
    out = {}
    for monom, coeff in p.terms():
        # exact-Q guard (review r1 note: a float TConst would silently
        # coerce here; the in-memory model types TConst.value as object,
        # so the checker owns this refusal)
        if not sp.sympify(coeff).is_Rational:
            fails.add(scope_id, where,
                      f"non-rational coefficient {coeff!r} — jet "
                      "arithmetic is exact-Q only")
            return None
        out[_jd_trim(monom)] = sp.Rational(coeff)
    return out


def _jet_tree_fragment(t) -> bool:
    """The index-free tree fragment (const/var/add/mul/sub) — the term
    domain shared with the staged polynomialCanonicalEq realization
    (PNorm's idx-free discipline; jet-v1 review r1 SF-2)."""
    if isinstance(t, (TConst, TVar)):
        return True
    if isinstance(t, (TAdd, TMul, TSub)):
        return _jet_tree_fragment(t.l) and _jet_tree_fragment(t.r)
    return False


def _iter_proof(p):
    """Every node of a proof tree (the emit-side collect_proof walk)."""
    yield p
    for attr in ("premise", "left", "right", "eq", "body", "regionProof",
                 "l", "r"):
        child = getattr(p, attr, None)
        if child is not None and hasattr(child, "concludes"):
            yield from _iter_proof(child)
    for attr in ("premises", "components"):
        for child in getattr(p, attr, ()) or ():
            yield from _iter_proof(child)


def check_jet_bindings(root, fails: Failures):
    """[J4] (jet-v1 review round 1, D-A repair): integral-wire binding
    FUNCTIONALITY, certificate-global — every PIntMono binding of one
    wire carries value-identical integrands, so the certificate's
    declared binding set is a function of wires. The certificate's
    meaning theorem quantifies over environments satisfying every
    declared binding AND every pre hypothesis (the family-v1
    declared-hypothesis pattern); [J4] makes that binding set
    well-defined. It deliberately does NOT force freshness of bound
    wires from `pre` — pre-atoms about bound wires are hypotheses about
    the bound denotations (the Wirtinger row is exactly one), and an
    inconsistent hypothesis set yields a vacuous, never an unsound,
    certificate under the declared-environment semantics (contract §5)."""
    seen = {}
    for node in _iter_proof(root):
        if not isinstance(node, PIntMono):
            continue
        try:
            q = sp.expand(term_to_sympy(node.integrand, {}))
        except (TypeError, ValueError):
            continue  # the node's own clause records the failure
        if node.int_wire in seen:
            if sp.expand(seen[node.int_wire] - q) != 0:
                fails.add("intmono.duplicate-binding", "certificate",
                          f"wire {node.int_wire!r} bound to two "
                          "value-distinct integrands ([J4] binding "
                          "functionality)")
        else:
            seen[node.int_wire] = q


def check_jet_frame(frame, wire_names: set, fails: Failures, where: str):
    """[J0]: >= 1 jet wire; pairwise distinct; declared; no hole."""
    if not isinstance(frame, JetFrame) or not frame.wires:
        fails.add("jet.frame", where, "frame must carry >= 1 jet wire")
        return False
    ok = True
    if len(set(frame.wires)) != len(frame.wires):
        fails.add("jet.frame", where, "frame wires must be pairwise distinct")
        ok = False
    if HOLE in frame.wires:
        fails.add("jet.frame", where, "the predicate hole is not a jet wire")
        ok = False
    extra = set(frame.wires) - wire_names
    if extra:
        fails.add("jet.frame", where, f"unknown frame wires {sorted(extra)}")
        ok = False
    h = _linkage_hypernet()
    if h is not None:
        dt = {w.name: w.dtype for w in h.wires}
        bad = [w for w in frame.wires if dt.get(w) not in (None, "Q")]
        if bad:
            fails.add("jet.frame", where,
                      f"frame wires must be exact-Q scalars, got "
                      f"{[(w, dt[w]) for w in bad]}")
            ok = False
    return ok


def check_jet_div(node: PJetDiv, wire_names: set, fails: Failures,
                  where="root"):
    """[J1]: scopes + D_x(flux) = p exactly, with the top-coordinate
    overflow rejection (flux of positive degree in u_k has no divergence
    witness inside the frame). Root-only in jet-v1 (contract SS1.3:
    nothing consumes a jet judgment as a premise — conservativity)."""
    if where != "root":
        fails.add("jet.root-only", where,
                  "PJetDiv is only legal at root in jet-v1")
        return
    j = node.concludes
    if not isinstance(j, JDiv):
        fails.add("jet.concludes", where, "PJetDiv must conclude a JDiv")
        return
    if not check_jet_frame(j.frame, wire_names, fails, where):
        return
    nv = len(j.frame.wires)
    p = _jet_dict(j.p, j.frame, fails, where + ".p", "jet.scope")
    fl = _jet_dict(node.flux, j.frame, fails, where + ".flux", "jet.scope")
    if p is None or fl is None:
        return
    dxf = _jd_dx(fl)
    over = sorted(m for m in dxf if len(m) > nv)
    if over:
        fails.add("jet.dx-overflow", where,
                  f"D_x(flux) needs u_{nv} (outside the frame): "
                  f"monomials {over[:3]} — size the frame at k >= "
                  "deg_jet(flux) + 1")
        return
    if dxf != p:
        fails.add("jet.dx-mismatch", where,
                  "D_x(flux) != p coefficientwise (isTotalDerivative)")


def check_functional_deriv(node: PFunctionalDeriv, wire_names: set,
                           fails: Failures, where="root"):
    """[J2]: scopes + the R1 recompute
    g = sum_j de/du_j * D_x^j(chart), exact. Root-only, leaf."""
    if where != "root":
        fails.add("jet.root-only", where,
                  "PFunctionalDeriv is only legal at root in jet-v1")
        return
    j = node.concludes
    if not isinstance(j, JEvo):
        fails.add("jet.concludes", where,
                  "PFunctionalDeriv must conclude a JEvo")
        return
    if not check_jet_frame(j.frame, wire_names, fails, where):
        return
    nv = len(j.frame.wires)
    g = _jet_dict(j.g, j.frame, fails, where + ".g", "jet.scope")
    e = _jet_dict(j.e, j.frame, fails, where + ".e", "jet.scope")
    ch = _jet_dict(j.chart, j.frame, fails, where + ".chart", "jet.scope")
    if g is None or e is None or ch is None:
        return
    acc = {}
    d = ch
    for jj in range(nv):
        de = _jd_diff(e, jj)
        if de:
            acc = _jd_add(acc, _jd_mul(de, d))
        d = _jd_dx(d)
    if acc != g:
        fails.add("jet.evo-recompute", where,
                  "recomputed evolution integrand differs from g "
                  "(isEvolutionIntegrand)")
