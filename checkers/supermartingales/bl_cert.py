"""Certificate data model for the Bernstein Logic v0 reference checker.

JSON-agnostic in-memory representation: frozen dataclasses mirroring the
geolog theory stack (designv3/PiecewisePolynomialLogicCertificate.geolog)
layer by layer — Term / Formula / Judgment / Proof over a Hypernet — at toy
scale.  The REAL wire format is bernfmt (paper sec:wireformat Level 1);
any serialization in this package is a THROWAWAY inspection dump.

v0 simplifications (documented deviations; see README.md deviation table):
  S1  single numeric tower: all constants are sympy Rationals; dtype tags
      ('Q', 'B') are carried on wires and checked at primitive boundaries,
      but Term arithmetic is dtype-blind (B embeds as {0,1} in Q; the toy is
      exact everywhere, so iota is the identity on values).
  S2  Cell complexes are lists of REGION-ENCODED closed cells (simplex +
      extension set), because the example's sign complex Sigma_pm has
      unbounded cells, which def:simpc's compact vertex-tuple simplices
      cannot express (finding F6).  R(conv(0,1), {1}) = {h <= 0} and
      R(conv(-1,0), {0}) = {h >= 0} recover the two sign cells exactly.
  S3  sp[Cell] uses the M4-REVISED one-hot form (BUILD-PLAN risk M4):
      OR_i (a in cl(C_i)  AND  b_i = 1  AND  AND_{j != i} b_j = 0),
      which coincides with the paper's form on Sigma_pm.
  R1  OrECtx replaces the printed OrE: the printed rule (paper + geolog
      ax/applicable/POrE/pre) requires the conclusion's pre to be LITERALLY
      the disjunction, which cannot consume a disjunctive conjunct inside
      Phi AND SP_H; see README findings F1.
  R2  EqElim carries a `flipped` flag (semantically free, since = is
      symmetric); without it the example is unclosable because sp-facts all
      orient equations wire-first; see README findings F2.
  R3  Farkas premises are sub-PROOFS (each concluding an atom t <= 0) rather
      than pre-subconjunct references as in geolog's PFarkas; the geolog
      form is recoverable by Ax+AndE sub-proofs.  All atoms canonically
      (t <= 0)-shaped; see README findings F3/F4 for why <=-shapes are
      forced.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional, Union

import sympy as sp
from sympy import Rational

# =========================================================================
# Terms
# =========================================================================

class Term:
    """Abstract term: wires, rational constants, +, *, - (paper sec:formulas)."""


@dataclass(frozen=True)
class TConst(Term):
    value: object  # sympy Rational / Integer

    def __repr__(self):
        return f"TConst({self.value})"


@dataclass(frozen=True)
class TVar(Term):
    wire: str

    def __repr__(self):
        return f"TVar({self.wire})"


@dataclass(frozen=True)
class TAdd(Term):
    l: Term
    r: Term


@dataclass(frozen=True)
class TMul(Term):
    l: Term
    r: Term


@dataclass(frozen=True)
class TSub(Term):
    l: Term
    r: Term


@dataclass(frozen=True)
class TNeg(Term):
    """Unary negation (Lean `Term.neg`; wire pool tag 0x06).  Present in
    the Lean/wire term grammar from the start; joined the python model
    with the wire/python parity pass (2026-07-19) because the
    ge-polarity reading of `syzygyConclusionForm` — conclusion = -e,
    post = (e >= 0) — is only expressible with a syntactic negation
    node.  canon_term never PRODUCES TNeg (the canonical AST stays in
    sum-of-monomials form); it appears where a producer chooses the
    ge-flip conclusion reading."""
    t: Term

    def __repr__(self):
        return f"TNeg({self.t!r})"


@dataclass(frozen=True)
class TIdx(Term):
    """Scalar component i of a rank-1 term (the degenerate case of the
    einsum contraction primitive; wire pool tag 0x07; geolog TIdx).  The producer
    only ever indexes wires directly: t is TVar in all emitted certificates,
    matching the Lean bridge's asCoordPoly? remap surface."""
    t: Term
    i: int

    def __repr__(self):
        return f"TIdx({self.t!r}, {self.i})"


@dataclass(frozen=True)
class TEinsum(Term):
    """terms-v1 (BINARY.md §6.1 tag 0x08): term-level
    tensor-product-and-contraction per the Tensors design sketch
    (David "davidad" Dalrymple).
    `extents[m]` is index m's extent; each input pairs a term with its
    axis->index binding tuple; `out_bindings` is the ordered, distinct
    output-axis tuple. Exact-only. Reference-checker scope: symbolic /
    ground expansion supports TVar tensor children and rank-0 children;
    composite tensor children await the X2 rule seatings (loud
    TypeError, never a silent skip)."""
    extents: tuple        # tuple[int, ...]
    inputs: tuple         # tuple[(Term, tuple[int, ...]), ...], >= 1
    out_bindings: tuple   # tuple[int, ...], pairwise distinct


@dataclass(frozen=True)
class TPoly(Term):
    """terms-v1 (BINARY.md §6.1 tag 0x09; memo register 2): a
    standard-form coefficient tensor — (domain, basis, support, coeffs)
    as manifest data. basis in {"monomial", "bernstein"}; domain is a
    Simplex iff basis == "bernstein". Support entries are
    (wire, component) with component None = the scalar wire itself
    (v0 univariate style) or an int = the G1 projection idx(wire, c).
    Entries are ((alpha, coeff), ...) in STRICTLY ascending numeric lex
    on alpha, no zero coefficients; len(alpha) = n_vars (monomial) /
    n_vars + 1 (bernstein). Coefficient convention: control points —
    p = sum b_alpha * multinom(d, alpha) * lambda^alpha (the reference-
    kernel convention, BINARY.md §6.1)."""
    basis: str
    domain: object        # Simplex | None
    degree: int
    support: tuple        # tuple[(wire, int|None), ...]
    entries: tuple        # tuple[(tuple[int, ...], Rational), ...]


def tpoly_wf_errors(p: TPoly):
    """The §6.1 shallow well-formedness rules, as a list of violation
    strings (empty = WF). Mirrors the wire readers' parse-time checks so
    in-memory fixtures are held to the same discipline."""
    errs = []
    if p.basis not in ("monomial", "bernstein"):
        errs.append(f"unknown basis {p.basis!r}")
        return errs
    if (p.domain is not None) != (p.basis == "bernstein"):
        errs.append("domain present iff basis == bernstein")
        return errs
    if len(set(p.support)) != len(p.support):
        errs.append("support entries must be pairwise distinct")
    if not p.support:
        errs.append("n_vars must be >= 1")
        return errs
    wires_scalar = {w for w, c in p.support if c is None}
    wires_comp = {w for w, c in p.support if c is not None}
    if wires_scalar & wires_comp:
        errs.append("support alias: scalar-use and component forms of one "
                    f"wire in one frame ({sorted(wires_scalar & wires_comp)})")
    n_vars = len(p.support)
    index_len = n_vars + 1 if p.basis == "bernstein" else n_vars
    if p.basis == "bernstein":
        if len(p.domain.vertices) != n_vars + 1:
            errs.append("domain vertex count != n_vars + 1")
        elif p.domain.vertices and len(p.domain.vertices[0]) != n_vars:
            errs.append("domain ambient dim != n_vars")
    prev = None
    max_total = 0
    for alpha, coeff in p.entries:
        if len(alpha) != index_len:
            errs.append(f"multi-index {alpha} length != {index_len}")
            break
        if any(a < 0 or a > 0xFFFF for a in alpha):
            errs.append(f"multi-index slot out of u16 range: {alpha}")
        if coeff == 0:
            errs.append(f"zero coefficient at {alpha}")
        if prev is not None and tuple(prev) >= tuple(alpha):
            errs.append(f"entries not strictly ascending at {alpha}")
        total = sum(alpha)
        if p.basis == "bernstein" and total != p.degree:
            errs.append(f"bernstein index {alpha} sums to {total} != "
                        f"degree {p.degree}")
        max_total = max(max_total, total)
        prev = alpha
    if p.basis == "monomial" and max_total != p.degree:
        errs.append(f"monomial degree cross-check: max total {max_total} "
                    f"!= stored degree {p.degree}")
    return errs


def barycentric_exprs(vertices, xs):
    """The barycentric coordinates lambda_v(x) of the simplex `vertices`
    as exact sympy expressions in the coordinate symbols `xs` — affine,
    total on all of Q^n. Raises ValueError on a degenerate simplex (the
    §6.1 checker obligation: affine independence)."""
    n = len(xs)
    assert len(vertices) == n + 1, (len(vertices), n)
    M = sp.Matrix([[sp.Rational(vertices[j][i]) for j in range(n + 1)]
                   for i in range(n)] + [[sp.Integer(1)] * (n + 1)])
    if M.det() == 0:
        raise ValueError("degenerate Bernstein domain: vertices are "
                         "affinely dependent")
    rhs = sp.Matrix(list(xs) + [sp.Integer(1)])
    lam = M.solve(rhs)
    return [sp.expand(lam[v]) for v in range(n + 1)]


def _support_symbol(entry, sym):
    wire, comp = entry
    name = wire if comp is None else idx_symbol_name(wire, comp)
    if name not in sym:
        sym[name] = sp.Symbol(name)
    return sym[name]


def tpoly_to_sympy(p: TPoly, sym):
    """Total evaluation semantics of a poly record (BINARY.md §6.1) as a
    sympy expression over the support coordinate symbols — the same
    symbol convention as term_to_sympy, so downstream scope bookkeeping
    is shared. Raises ValueError on WF violations or degenerate domain
    (checker obligations surface loudly, never as wrong values)."""
    errs = tpoly_wf_errors(p)
    if errs:
        raise ValueError(f"non-WF poly record: {errs}")
    xs = [_support_symbol(e, sym) for e in p.support]
    if p.basis == "monomial":
        acc = sp.Integer(0)
        for alpha, coeff in p.entries:
            term = sp.Rational(coeff)
            for x, a in zip(xs, alpha):
                term *= x ** a
            acc += term
        return sp.expand(acc)
    lams = barycentric_exprs(p.domain.vertices, xs)
    d = p.degree
    acc = sp.Integer(0)
    for alpha, coeff in p.entries:
        term = sp.Rational(coeff) * sp.Integer(_multinom(d, alpha))
        for lam, a in zip(lams, alpha):
            term *= lam ** a
        acc += term
    return sp.expand(acc)


def _multinom(d, alpha):
    assert sum(alpha) == d, (d, alpha)
    r = sp.factorial(d)
    for a in alpha:
        r //= sp.factorial(a)
    return int(r)


def _einsum_component(t: Term, idxvals, sym):
    """Scalar component of einsum child `t` at index values `idxvals`
    (reference-checker child scope: TVar tensors, rank-0 terms)."""
    if isinstance(t, TVar):
        if not idxvals:
            if t.wire not in sym:
                sym[t.wire] = sp.Symbol(t.wire)
            return sym[t.wire]
        if len(idxvals) == 1:
            name = idx_symbol_name(t.wire, idxvals[0])
            if name not in sym:
                sym[name] = sp.Symbol(name)
            return sym[name]
        name = f"{t.wire}__" + "_".join(str(i) for i in idxvals)
        if name not in sym:
            sym[name] = sp.Symbol(name)
        return sym[name]
    if not idxvals:
        return term_to_sympy(t, sym)
    raise TypeError(f"einsum child outside the reference-checker scope "
                    f"(TVar tensors / rank-0 terms): {t}")


def teinsum_to_sympy(t: TEinsum, sym):
    """Scalar (out_rank == 0) einsum expansion: the §6.1 semantics sum,
    written out. Tensor-valued einsums (out_rank > 0) have no scalar
    sympy image — TypeError, and their atoms are structural material
    until the X2 seatings."""
    if len(t.inputs) < 1:
        raise ValueError("einsum requires n_inputs >= 1")
    if t.out_bindings:
        raise TypeError("tensor-valued einsum has no scalar sympy image")
    m = len(t.extents)
    from itertools import product as _prod
    total = sp.Integer(0)
    for assignment in _prod(*[range(int(e)) for e in t.extents]) \
            if m else [()]:
        prod_term = sp.Integer(1)
        for child, bindings in t.inputs:
            vals = [assignment[b] for b in bindings]
            prod_term *= _einsum_component(child, vals, sym)
        total += prod_term
    return sp.expand(total)


def idx_symbol_name(wire: str, i: int) -> str:
    """The pinned wire-coordinate <-> sympy-symbol naming convention shared
    by term_to_sympy and the multivariate BernCone recomputation."""
    return f"{wire}__{i}"


def term_to_sympy(t: Term, sym):
    """sym: dict wire-name -> sympy Symbol (created on demand).
    TIdx(TVar(w), i) maps to the pinned coordinate symbol idx_symbol_name;
    the key in `sym` is the same string, so scope bookkeeping downstream
    (bl_checker PBernCone) can distinguish bare wires from coordinates."""
    if isinstance(t, TConst):
        return sp.sympify(t.value)
    if isinstance(t, TVar):
        if t.wire not in sym:
            sym[t.wire] = sp.Symbol(t.wire)
        return sym[t.wire]
    if isinstance(t, TIdx):
        if not isinstance(t.t, TVar):
            raise TypeError(f"TIdx base must be a wire in v0+G1 emission: {t}")
        name = idx_symbol_name(t.t.wire, t.i)
        if name not in sym:
            sym[name] = sp.Symbol(name)
        return sym[name]
    if isinstance(t, TAdd):
        return term_to_sympy(t.l, sym) + term_to_sympy(t.r, sym)
    if isinstance(t, TMul):
        return term_to_sympy(t.l, sym) * term_to_sympy(t.r, sym)
    if isinstance(t, TSub):
        return term_to_sympy(t.l, sym) - term_to_sympy(t.r, sym)
    if isinstance(t, TNeg):
        return -term_to_sympy(t.t, sym)
    if isinstance(t, TPoly):
        return tpoly_to_sympy(t, sym)
    if isinstance(t, TEinsum):
        return teinsum_to_sympy(t, sym)
    raise TypeError(t)


def term_free_wires(t: Term) -> frozenset:
    if isinstance(t, TConst):
        return frozenset()
    if isinstance(t, TVar):
        return frozenset({t.wire})
    if isinstance(t, TIdx):
        return term_free_wires(t.t)   # geolog ax/FreeInTerm_idx
    if isinstance(t, (TAdd, TMul, TSub)):
        return term_free_wires(t.l) | term_free_wires(t.r)
    if isinstance(t, TNeg):
        return term_free_wires(t.t)
    if isinstance(t, TPoly):
        return frozenset(w for w, _ in t.support)
    if isinstance(t, TEinsum):
        out = frozenset()
        for child, _ in t.inputs:
            out |= term_free_wires(child)
        return out
    raise TypeError(t)


def term_subst(t: Term, wire: str, repl: Term) -> Term:
    if isinstance(t, TConst):
        return t
    if isinstance(t, TVar):
        return repl if t.wire == wire else t
    if isinstance(t, TIdx):
        return TIdx(term_subst(t.t, wire, repl), t.i)
    if isinstance(t, TAdd):
        return TAdd(term_subst(t.l, wire, repl), term_subst(t.r, wire, repl))
    if isinstance(t, TMul):
        return TMul(term_subst(t.l, wire, repl), term_subst(t.r, wire, repl))
    if isinstance(t, TSub):
        return TSub(term_subst(t.l, wire, repl), term_subst(t.r, wire, repl))
    if isinstance(t, TNeg):
        return TNeg(term_subst(t.t, wire, repl))
    if isinstance(t, TPoly):
        if wire not in {w for w, _ in t.support}:
            return t
        if isinstance(repl, TVar):
            new_support = tuple((repl.wire if w == wire else w, c)
                                for w, c in t.support)
            if len(set(new_support)) != len(new_support):
                raise TypeError(f"substitution aliases poly support: {t}")
            return TPoly(t.basis, t.domain, t.degree, new_support, t.entries)
        raise TypeError("substituting a non-wire term into a poly support "
                        f"is outside the v1 producer subset: {t}")
    if isinstance(t, TEinsum):
        return TEinsum(t.extents,
                       tuple((term_subst(c, wire, repl), b)
                             for c, b in t.inputs),
                       t.out_bindings)
    raise TypeError(t)


def term_idx_profile(t: Term):
    """(bare_wires, {(wire, i), ...}) — which wires occur bare vs indexed.
    Used by the multivariate BernCone check to enforce the G1 discipline:
    over an n>1 region, the polynomial's region wire occurs only under TIdx."""
    if isinstance(t, TConst):
        return frozenset(), frozenset()
    if isinstance(t, TVar):
        return frozenset({t.wire}), frozenset()
    if isinstance(t, TIdx):
        if not isinstance(t.t, TVar):
            raise TypeError(f"TIdx base must be a wire: {t}")
        return frozenset(), frozenset({(t.t.wire, t.i)})
    if isinstance(t, (TAdd, TMul, TSub)):
        bl, il = term_idx_profile(t.l)
        br, ir = term_idx_profile(t.r)
        return bl | br, il | ir
    if isinstance(t, TNeg):
        return term_idx_profile(t.t)
    if isinstance(t, TPoly):
        bare = frozenset(w for w, c in t.support if c is None)
        idxd = frozenset((w, c) for w, c in t.support if c is not None)
        return bare, idxd
    # TEinsum deliberately absent: the profile serves BernCone payload
    # scoping, where einsum roots are rejected before profiling
    # (BINARY.md §6.2 discipline); reaching here is a bug — stay loud.
    raise TypeError(t)


# ---- canonical polynomial term ASTs -------------------------------------
#
# canon(expr): expand over Q; clear denominators by the (positive) lcm and
# divide by the (positive) gcd of integer coefficients -> primitive integer
# form, SIGN PRESERVED (sign is semantic content in an inequality atom);
# monomials sorted by (-total_degree, variable string); AST built as
# right-nested TAdd of TMul(TConst(c), right-nested var product).
# Both emitter and checker use this single function; "canonical" in this
# package means precisely its output.  (Leg C will own the real canonical
# form; nothing downstream depends on this particular order, only on its
# determinism.)

def canon_sympy(expr):
    """Primitive-integer-form of a Q-polynomial sympy expr (sign preserved)."""
    # rational=True is essential: bare nsimplify's numeric search can
    # replace an exact Rational by a radical (see bl_bernstein.py, the
    # differential-harness catch); rational=True only converts Floats.
    e = sp.expand(sp.nsimplify(sp.together(expr), rational=True))
    if e == 0:
        return sp.Integer(0)
    syms = sorted(e.free_symbols, key=lambda s: s.name)
    p = sp.Poly(e, *syms) if syms else None
    coeffs = [sp.Rational(c) for c in (p.coeffs() if syms else [e])]
    denl = sp.ilcm(*[c.q for c in coeffs]) if len(coeffs) > 1 else coeffs[0].q
    nums = [c * denl for c in coeffs]
    g = sp.igcd(*[abs(x) for x in nums]) if len(nums) > 1 else abs(nums[0])
    scale = sp.Rational(denl, g)
    return sp.expand(e * scale)


def wire_of_sym_from(sym, wire_names=None) -> dict:
    """Inverse of term_to_sympy's symbol registry: {Symbol: Term}.  Keys in
    `sym` that follow the idx_symbol_name convention ('<wire>__<i>', with
    <wire> a known wire when wire_names is given) map back to
    TIdx(TVar(wire), i); everything else maps to TVar(name).  Reference-
    checker convenience only (the Lean checker is structural — no name
    parsing exists on the certified surface)."""
    out = {}
    for name, symbol in sym.items():
        term = None
        if "__" in name:
            base, _, tail = name.rpartition("__")
            if base and tail.isdigit() and (wire_names is None or base in wire_names):
                term = TIdx(TVar(base), int(tail))
        out[symbol] = term if term is not None else TVar(name)
    return out


def poly_term(expr, wire_of_sym=None) -> Term:
    """Canonical-SHAPE Term AST of a sympy polynomial, WITHOUT rescaling.

    Use for semantic-content terms: equation right-hand sides (sp-facts),
    Poly primitive parameters — anywhere the polynomial's VALUE matters.
    canon_term (primitive-integer rescaling) is only sound for (t <= 0)
    atoms, whose meaning is invariant under positive scaling; using it on
    an equation RHS silently rescales the dynamics (caught 2026-07-16 by
    the piecewise-vs-certificate artifact pair; see README findings F7).
    """
    return _term_ast(sp.expand(sp.nsimplify(expr, rational=True)), wire_of_sym)


def canon_term(expr, wire_of_sym=None) -> Term:
    """Canonical Term AST of the PRIMITIVE-INTEGER form (positive rescaling;
    for inequality-atom bodies only — see poly_term)."""
    return _term_ast(canon_sympy(expr), wire_of_sym)


def _term_ast(e, wire_of_sym=None) -> Term:
    syms = sorted(e.free_symbols, key=lambda s: s.name)
    if not syms:
        return TConst(sp.Rational(e))
    p = sp.Poly(e, *syms)
    monos = []
    for monom, coeff in p.terms():
        deg = sum(monom)
        varstr = ",".join(f"{syms[i].name}^{monom[i]}" for i in range(len(syms)) if monom[i])
        monos.append((-deg, varstr, monom, sp.Rational(coeff)))
    monos.sort(key=lambda m: (m[0], m[1]))
    parts = []
    for _, _, monom, coeff in monos:
        vprod = None
        for i in range(len(syms)):
            for _ in range(monom[i]):
                w = wire_of_sym[syms[i]] if wire_of_sym else syms[i].name
                # wire_of_sym values may be wire NAMES or full Terms (the
                # TIdx coordinate case, G1): a Term is used verbatim.
                v = w if isinstance(w, Term) else TVar(w)
                vprod = v if vprod is None else TMul(vprod, v)
        parts.append(TConst(coeff) if vprod is None else TMul(TConst(coeff), vprod))
    out = parts[-1]
    for pt in reversed(parts[:-1]):
        out = TAdd(pt, out)
    return out


# =========================================================================
# Simplices, extension sets, regions
# =========================================================================

@dataclass(frozen=True)
class Simplex:
    """n-simplex: tuple of n+1 vertices, each a tuple of n Rationals."""
    vertices: tuple  # tuple[tuple[Rational, ...], ...]

    @property
    def n(self):
        return len(self.vertices) - 1

    def __repr__(self):
        vs = ",".join("(" + ",".join(str(c) for c in v) + ")" for v in self.vertices)
        return f"Simplex[{vs}]"


def simplex1d(a, b) -> Simplex:
    return Simplex(((Rational(a),), (Rational(b),)))


# =========================================================================
# Formulas
# =========================================================================

class Formula:
    pass


@dataclass(frozen=True)
class FAtom(Formula):
    op: str  # one of '<=', '<', '=', '>=', '>'
    l: Term
    r: Term

    def __repr__(self):
        return f"({self.l!r} {self.op} {self.r!r})"


@dataclass(frozen=True)
class FAnd(Formula):
    l: Formula
    r: Formula


@dataclass(frozen=True)
class FOr(Formula):
    l: Formula
    r: Formula


@dataclass(frozen=True)
class FTrue(Formula):
    pass


@dataclass(frozen=True)
class FFalse(Formula):
    pass


@dataclass(frozen=True)
class FInRegion(Formula):
    """Region atom  t in R(simplex, S)  (paper sec:formulas, sec:gen-bern-setup).

    For n = 1 the term is the single ambient coordinate; general rank-1
    tensor terms are BUILD-PLAN D2 territory and out of v0 scope."""
    term: Term
    simplex: Simplex
    S: frozenset  # extended vertex indices, PROPER subset of {0..n}


def formula_subst(f: Formula, wire: str, repl: Term) -> Formula:
    if isinstance(f, FAtom):
        return FAtom(f.op, term_subst(f.l, wire, repl), term_subst(f.r, wire, repl))
    if isinstance(f, FAnd):
        return FAnd(formula_subst(f.l, wire, repl), formula_subst(f.r, wire, repl))
    if isinstance(f, FOr):
        return FOr(formula_subst(f.l, wire, repl), formula_subst(f.r, wire, repl))
    if isinstance(f, (FTrue, FFalse)):
        return f
    if isinstance(f, FInRegion):
        return FInRegion(term_subst(f.term, wire, repl), f.simplex, f.S)
    raise TypeError(f)


def formula_free_wires(f: Formula) -> frozenset:
    if isinstance(f, FAtom):
        return term_free_wires(f.l) | term_free_wires(f.r)
    if isinstance(f, (FAnd, FOr)):
        return formula_free_wires(f.l) | formula_free_wires(f.r)
    if isinstance(f, (FTrue, FFalse)):
        return frozenset()
    if isinstance(f, FInRegion):
        return term_free_wires(f.term)
    raise TypeError(f)


# ---- conjunction paths ---------------------------------------------------

def conj_get(f: Formula, path: tuple) -> Formula:
    """Fetch the sub-formula at `path` in the AND-tree of f ('l'/'r' steps)."""
    for step in path:
        if not isinstance(f, FAnd):
            raise KeyError(f"path step {step} into non-conjunction {type(f).__name__}")
        f = f.l if step == "l" else f.r
    return f


def conj_replace(f: Formula, path: tuple, new: Formula) -> Formula:
    if not path:
        return new
    if not isinstance(f, FAnd):
        raise KeyError("path into non-conjunction")
    if path[0] == "l":
        return FAnd(conj_replace(f.l, path[1:], new), f.r)
    return FAnd(f.l, conj_replace(f.r, path[1:], new))


# =========================================================================
# barycentric halfspace canonical form (ConvIntro/ConvElim's shared spec)
# =========================================================================

def barycentric_halfspace_form(term: Term, simplex: Simplex, S: frozenset) -> Formula:
    """The canonical halfspace conjunction equivalent to FInRegion(term, ...).

    One atom per vertex index i (in index order, right-nested FAnd):
      i in S    ->  ( canon(  lambda_i(t)) <= 0 )     [extended: lambda_i <= 0]
      i in Sbar ->  ( canon(- lambda_i(t)) <= 0 )     [core:     lambda_i >= 0]
    ALL atoms are (poly <= 0)-shaped: the calculus as printed has no rule
    that flips an atom across <=/>= (finding F4), so a single canonical shape
    is the only way proofs can connect atoms syntactically.
    n = 1 only in v0 (see FInRegion).
    """
    from bl_bernstein import barycentric_coords
    assert simplex.n == 1, "v0 toy: 1D regions only"
    xsym = sp.Symbol("_x_")
    lams = barycentric_coords(simplex.vertices, (xsym,))
    sym = {}
    t_expr = term_to_sympy(term, sym)
    atoms = []
    for i, lam in enumerate(lams):
        body = lam if i in S else -lam
        expr = body.subs(xsym, t_expr)
        atoms.append(FAtom("<=", canon_term(expr), TConst(Rational(0))))
    out = atoms[-1]
    for a in reversed(atoms[:-1]):
        out = FAnd(a, out)
    return out


# =========================================================================
# Hypernet
# =========================================================================

@dataclass(frozen=True)
class Wire:
    name: str
    dtype: str  # 'Q' | 'B'


class PrimApp:
    pass


@dataclass(frozen=True)
class PCopy(PrimApp):
    inp: str
    outs: tuple  # k output wire names


@dataclass(frozen=True)
class PPoly(PrimApp):
    """Ergonomic Poly(q) primitive (paper sec:cert-prims): out = q(inputs),
    exact over Q.  q is stored as a canonical Term over the INPUT WIRES."""
    inps: tuple
    out: str
    q: Term


@dataclass(frozen=True)
class Cell:
    """A closed cell, region-encoded (deviation S2)."""
    simplex: Simplex
    S: frozenset


@dataclass(frozen=True)
class PCell(PrimApp):
    inp: str
    outs: tuple  # N indicator wires, one per cell
    cells: tuple  # tuple[Cell, ...]


@dataclass(frozen=True)
class PCast(PrimApp):
    inp: str
    out: str


@dataclass(frozen=True)
class PDelete(PrimApp):
    inp: str


@dataclass(frozen=True)
class PRelu(PrimApp):
    """Packaged ReLU — the first ADMISSIBLE primitive (conservative-
    extension memo register 1, endorsed 2026-07-16; wire
    app tag 10, BINARY.md sec 5.2; Lean `PrimApp.relu` + the three
    obligations at ReluExpansion.lean).  The toy mirrors the
    discharged-warrant profile exactly: one scalar Q wire in, one out
    (Lean shape [1], dtype Q — the profile at which `relu_projection`
    and `reluExpansion_typing` are proven; positive total size is
    structural here, so `reluLinked`'s size gate is trivially met)."""
    preact: str
    post: str


@dataclass(frozen=True)
class Hypernet:
    wires: tuple  # tuple[Wire, ...]
    prims: tuple  # tuple[PrimApp, ...]
    inputs: tuple  # input wire names
    outputs: tuple  # output wire names


def prim_inputs(p: PrimApp) -> tuple:
    if isinstance(p, PCopy):
        return (p.inp,)
    if isinstance(p, PPoly):
        return p.inps
    if isinstance(p, PCell):
        return (p.inp,)
    if isinstance(p, PCast):
        return (p.inp,)
    if isinstance(p, PDelete):
        return (p.inp,)
    if isinstance(p, PRelu):
        return (p.preact,)
    raise TypeError(p)


def prim_outputs(p: PrimApp) -> tuple:
    if isinstance(p, PCopy):
        return p.outs
    if isinstance(p, PPoly):
        return (p.out,)
    if isinstance(p, PCell):
        return p.outs
    if isinstance(p, PCast):
        return (p.out,)
    if isinstance(p, PDelete):
        return ()
    if isinstance(p, PRelu):
        return (p.post,)
    raise TypeError(p)


# ---- sp-fact synthesis (the checker recomputes this; B4 discipline) ------

def sp_fact(p: PrimApp) -> Formula:
    if isinstance(p, PCopy):
        eqs = [FAtom("=", TVar(o), TVar(p.inp)) for o in p.outs]
        out = eqs[-1]
        for e in reversed(eqs[:-1]):
            out = FAnd(e, out)
        return out
    if isinstance(p, PPoly):
        return FAtom("=", TVar(p.out), p.q)
    if isinstance(p, PCell):
        # M4-revised one-hot disjuncts (deviation S3):
        #   OR_i ( inp in cl(C_i)  AND  b_i = 1  AND  AND_{j != i} b_j = 0 )
        disjuncts = []
        for i, cell in enumerate(p.cells):
            eqs = [FAtom("=", TVar(p.outs[i]), TConst(Rational(1)))]
            for j in range(len(p.cells)):
                if j != i:
                    eqs.append(FAtom("=", TVar(p.outs[j]), TConst(Rational(0))))
            inner = eqs[-1]
            for e in reversed(eqs[:-1]):
                inner = FAnd(e, inner)
            disjuncts.append(FAnd(FInRegion(TVar(p.inp), cell.simplex, cell.S), inner))
        out = disjuncts[-1]
        for d in reversed(disjuncts[:-1]):
            out = FOr(d, out)
        return out
    if isinstance(p, PCast):
        return FAtom("=", TVar(p.out), TVar(p.inp))
    if isinstance(p, PDelete):
        return FTrue()
    if isinstance(p, PRelu):
        # The DERIVED sp-fact (register 1): the two-case relation, the
        # exact Formula shape Lean's `PrimApp.spFact` emits at
        # single-entry shapes (Core/Catalogue.lean) — proven from the
        # expansion's sp-facts by `relu_projection`, never axiomatized:
        #   (preact <= 0 AND post = 0) OR (preact >= 0 AND post = preact)
        a_t = TVar(p.preact)
        return FOr(
            FAnd(FAtom("<=", a_t, TConst(Rational(0))),
                 FAtom("=", TVar(p.post), TConst(Rational(0)))),
            FAnd(FAtom(">=", a_t, TConst(Rational(0))),
                 FAtom("=", TVar(p.post), a_t)))
    raise TypeError(p)


# ---- the packaged ReLU's definitional expansion (Obligation U's data) ----
#
# The toy image of Lean `ReluExpansion.reluExpH` (copy;(id (x) Cell);
# Contract), rendered in the toy's own primitives: PCopy fan-out, the
# two-cell sign complex (region-encoded, deviation S2 — the same
# encodings X1 pins), PCast on the positive indicator, and the product
# as a PPoly.  `relu_expansion_prims` is the recompute source for the
# unfold-on-demand rule: the checker rebuilds the expansion's sp-facts
# from (preact, post, fresh) alone — the expansion is definitional, so
# it never rides the wire (recompute pattern; BINARY.md sec 5.2
# "Obligation U ... has NO wire representation").

RELU_SIMPLEX_NEG = Simplex(((Rational(0),), (Rational(1),)))
RELU_S_NEG = frozenset({1})     # R(conv(0,1), {1})  = {h <= 0}
RELU_SIMPLEX_POS = Simplex(((Rational(-1),), (Rational(0),)))
RELU_S_POS = frozenset({0})     # R(conv(-1,0), {0}) = {h >= 0}

RELU_UNFOLD_ARITY = 5           # (h1, h2, gneg, gpos, gq)


def relu_expansion_prims(preact: str, post: str, fresh: tuple) -> tuple:
    """The expansion composite's application list over `fresh` =
    (h1, h2, gneg, gpos, gq): copy the pre-activation, sign-split one
    copy, cast the positive indicator to Q, multiply.  Mirrors
    `reluExpH`'s six applications with the toy's reshape-free scalar
    wires (the [1]<->[] reshapes have no toy image; the rank-0 exact
    contract is the PPoly product)."""
    h1, h2, gneg, gpos, gq = fresh
    return (
        PCopy(preact, (h1, h2)),
        PCell(h2, (gneg, gpos),
              (Cell(RELU_SIMPLEX_NEG, RELU_S_NEG),
               Cell(RELU_SIMPLEX_POS, RELU_S_POS))),
        PCast(gpos, gq),
        PPoly((h1, gq), post, TMul(TVar(h1), TVar(gq))),
    )


def relu_expansion_spfacts(preact: str, post: str, fresh: tuple) -> Formula:
    """The expansion's sp-fact conjunction (same fold as sp_H over the
    virtual application list) — what the unfold rule adjoins to the
    premise's hypothesis over fresh internal wires."""
    prims = relu_expansion_prims(preact, post, fresh)
    facts = [sp_fact(q) for q in prims]
    out = facts[-1]
    for f in reversed(facts[:-1]):
        out = FAnd(f, out)
    return out


def sp_H(h: Hypernet) -> Formula:
    # Lean `Hypernet.spConjunction`: foldr (and . spFact) tt — the .tt
    # TERMINATOR rides every fold, empty or not (X2 design-review F-007:
    # the previous nonempty case dropped it, so python-shaped roots and
    # Lean-shaped roots disagreed under the exact-AST root check).
    out = FTrue()
    for f in reversed([sp_fact(p) for p in h.prims]):
        out = FAnd(f, out)
    return out


# =========================================================================
# Judgements and proof terms
# =========================================================================

@dataclass(frozen=True)
class Judgment:
    pre: Formula
    post: Formula


class Proof:
    """Every node carries `concludes: Judgment`; payloads mirror geolog's
    P<Rule> applicability data."""


@dataclass(frozen=True)
class PAx(Proof):
    concludes: Judgment


@dataclass(frozen=True)
class PAndE(Proof):
    concludes: Judgment
    premise: Proof
    which: str  # 'l' | 'r'


@dataclass(frozen=True)
class PAndI(Proof):
    concludes: Judgment
    l: Proof
    r: Proof


@dataclass(frozen=True)
class POrECtx(Proof):
    """PROPOSED REVISION R1 (see module docstring + README findings F1):
    context-carrying disjunction elimination.  `path` addresses an FOr
    conjunct inside the conclusion's pre AND-tree; each branch's pre is the
    conclusion's pre with that conjunct replaced by the respective disjunct.
    The printed OrE is the path=() special case.

    Admissibility over the plain core is REFUTED by kernel check
    (Admissible.lean: cx_not_derivable / orECtx_not_elaborable — the
    core never derives distributivity), so this constructor IS the core
    rule, realized exactly as drafted here;
    warrant = sound_orECtx (kernel-checked soundness, certified
    surface). Plain OrE = the path=() instance. Wire: tag 6 carries the
    path; disjuncts are recomputed from the pre — derivable data never
    rides the wire."""
    concludes: Judgment
    path: tuple
    left: Proof
    right: Proof


@dataclass(frozen=True)
class PCut(Proof):
    """Cut: Φ ⊢ χ,  Φ ∧ χ ⊢ Ψ  ⟹  Φ ⊢ Ψ  (geolog ll.754–771; wire tag 2).
    Added for the wire-level producer: wire-level Farkas is a LEAF whose entries
    are matched against pre-conjuncts, so a Farkas premise that is DERIVED
    (an EqElim image, not a pre-conjunct) routes through Cut — the left
    proof derives the atom, the right proof consumes it as the freshly
    adjoined pre-conjunct."""
    concludes: Judgment
    cutFormula: Formula
    left: Proof
    right: Proof


@dataclass(frozen=True)
class PEqRefl(Proof):
    """EqRefl (core; wire tag 23):
    post = (term = term); pre arbitrary (the Norm convention)."""
    concludes: Judgment
    term: Term


@dataclass(frozen=True)
class PEqSym(Proof):
    """EqSym (core; wire tag 24): premise post = (t = u);
    post = (u = t); pre preserved.  Replaces the toy's retired R2 `flipped`
    flag for all NEW emission (relu1d's flipped usage is grandfathered
    python-side; it has no wire image)."""
    concludes: Judgment
    premise: Proof
    termT: Term
    termU: Term


@dataclass(frozen=True)
class PEqElim(Proof):
    """Leibniz.  concludes.post = bodyForm[wire := termU],
    body.post = bodyForm[wire := termT], eq.post = (termT = termU) —
    or (termU = termT) when flipped (PROPOSED REVISION R2, findings F2)."""
    concludes: Judgment
    eq: Proof
    body: Proof
    wire: str
    termT: Term
    termU: Term
    bodyForm: Formula
    flipped: bool = False


@dataclass(frozen=True)
class PConvIntro(Proof):
    concludes: Judgment
    premise: Proof
    term: Term
    simplex: Simplex
    S: frozenset


@dataclass(frozen=True)
class PConvElim(Proof):
    concludes: Judgment
    premise: Proof
    term: Term
    simplex: Simplex
    S: frozenset


@dataclass(frozen=True)
class PBernCone(Proof):
    """The arithmetic-closure rule (paper sec:gen-bern-rule-statement).
    Coefficients are RECOMPUTED by the checker from (simplex, S, degree,
    polynomial) exactly as geolog's allForwardDiffBernCoeffsSatisfyP does;
    the emitter additionally STORES the computed per-(j,gamma) coefficient
    grid in `stored_grid` for inspection/cross-check (mission deliverable:
    'Bernstein coefficient vectors per cell')."""
    concludes: Judgment
    regionProof: Proof
    termX: Term
    simplex: Simplex
    S: frozenset
    degree: int
    polynomial: Term
    predicate: Formula          # formula over the placeholder wire '_hole'
    stored_grid: tuple = ()     # tuple[(j, gamma, Rational)], emitter-filled


@dataclass(frozen=True)
class PFarkas(Proof):
    """Admissible rule; deviation R3 (proof-premised form, findings F3).
    premises[i].post must be (t_i <= 0); check: lambdas >= 0 and
    canon(sum_i lambda_i * t_i) == conclusion (a canonical Term);
    post = (conclusion <= 0)."""
    concludes: Judgment
    premises: tuple  # tuple[Proof, ...]
    lambdas: tuple   # tuple[Rational, ...]
    conclusion: Term


@dataclass(frozen=True)
class PPromise(Proof):
    """CORE rule (the endorsement of 2026-07-16,
    verbatim: "endorsed - promise and syzygy can enter the core calculus,
    with smallgain admissible"; wire tag 25): the interface-promise cut,
    ctx-style (his 18:32 lean — POrECtx's path machinery reused).
    supplier.post == contract; `path` addresses the contract inside
    consumer's pre AND-tree; concludes.pre = consumer.pre with that
    conjunct replaced by supplier.pre; concludes.post = consumer.post.
    `iface` is the declared interface wire-name tuple; the two
    confinement side-conditions (contract wires within iface; supplier-pre
    wires shared with the blanked-slot context or the conclusion route
    through iface) are CHECKED but never consumed by soundness — the
    locality warrant (Lean: PPromiseData / sound_promise). The context
    formula is recomputed (conjReplace at FTrue), never carried."""
    concludes: Judgment
    supplier: Proof
    consumer: Proof
    contract: Formula
    path: tuple
    iface: tuple  # tuple[str, ...] wire names


@dataclass(frozen=True)
class PSyzygy(Proof):
    """CORE rule (same endorsement; wire tag 26): Newton's-third-law
    cancellation, dialect D. PFarkas's proof-premised shape lifted two
    ways: entry atoms come from COMPONENT conclusions (sub-proofs) or
    from equality sub-conjuncts of the composite pre (the compiled
    wiring; both polarities exposed, nonneg weights on each — free sign
    on '=' only, self-policing); atom polynomials unrestricted in degree.
    check: lambdas >= 0, each entry sourced as above, and
    canon(sum_i lambda_i * t_i) == conclusion exactly;
    post = (conclusion <= 0). Every component's pre must be a
    sub-conjunction of concludes.pre (premiseContains), and B14 extends
    to component-conclusion wires (a vacuously-held conclusion over a
    zero-size wire poisons the combination — Composition.lean header).
    Optional `theta`: the per-node robustness modulus, present iff this
    node is small-gain-shaped; zero proof-theoretic weight (header
    theta_ref = min over present thetas, H4 Cor. 6.2). SmallGain itself
    gets NO class here and NO tag: elaborate to PSyzygy at weights
    (1, lam, 1, 1) — the kernel-checked collapse smallGain_is_syzygy is
    the warrant."""
    concludes: Judgment
    components: tuple  # tuple[Proof, ...]
    lambdas: tuple     # tuple[Rational, ...]
    conclusion: Term
    theta: object = None  # Optional[Rational]


def smallgain_to_syzygy(concludes, e1, e2, m1, m2, lam, theta, conclusion):
    """The admissible SmallGain rule, realized as its elaboration (the
    only form that ever exists past a producer): components (e1, e2, m1,
    m2) = the two dissipation residual proofs and the two membership
    residual proofs, combined at weights (1, lam, 1, 1). Carries theta
    onto the node for the header's composite modulus."""
    return PSyzygy(concludes=concludes, components=(e1, e2, m1, m2),
                   lambdas=(1, lam, 1, 1), conclusion=conclusion,
                   theta=theta)


# =========================================================================
# X2 batch: arithAtom + norm (Lean core/admissible rules, previously
# unmirrored python-side) and the five ReLU/LiRPA rules (formerly
# vacuous; inhabited via the packaged-primitive route, Lean sec S8'''')
# =========================================================================


@dataclass(frozen=True)
class PArithAtom(Proof):
    """arithAtom (wire tag 10 in the PROOF section; Lean PArithAtomData).
    Relates an atom's DIRECT form (l op r) with its ZERO form
    ((l - r) op 0), same bowtie, literal TSub — never canon (the checker
    compares ASTs; Lean `atomicCompareZero` is `.atom b (.sub l r) 0`).
    variant: 'fold' = zero-form premise, direct conclusion;
    'unfold' = direct premise, zero-form conclusion.  op != '!=' (Lean
    notNE; the toy has no ne atom at all)."""
    concludes: Judgment
    premise: Proof
    termL: Term
    termR: Term
    op: str          # '<=', '<', '=', '>=', '>'
    variant: str     # 'fold' | 'unfold'


@dataclass(frozen=True)
class PNorm(Proof):
    """norm (wire tag 12; Lean PNormData).  post = (termL = termR),
    warranted by CANONICAL-FORM equality: both sides idx-free (Lean
    `polynomialCanonicalEq`'s gate) and equal as Q-polynomials
    (`l.toPoly = r.toPoly` — VALUE-preserving; nothing rescales).  Pre
    arbitrary (the EqRefl convention).  The toy's idx-free fragment is
    {TConst, TVar, TAdd, TMul, TSub}."""
    concludes: Judgment
    termL: Term
    termR: Term


@dataclass(frozen=True)
class PConstExact(Proof):
    """constExact (TIER-2 ADMISSIBLE; Lean PConstExactData; NO wire tag —
    wire realization rides the v1 payload window).  The closed
    exact-constant fact: premise-free |- (e1 op e2) for CLOSED (wire-free)
    scalar terms, op != '!=' (Lean notNE — a wireless ne-atom interprets
    to bottom under the M3 countermodel), decided by exact ground
    evaluation (Lean `Formula.evalClosed = some true`; the python checker
    evaluates both sides in sympy and requires no free symbols).  Pre
    arbitrary (the Norm convention).  Subsumes the PRatFact corner
    (e1 = const c, e2 = const 0; PConstExact is the deliberate
    generalization subsuming PRatFact) and with it
    retires the box-pair constant trick (mu*(x0-hi0) + mu*(lo0-x0)
    = mu*(lo0-hi0)) at producer sites that need a literal constant entry
    in a combination; until the v1 window, emission-bound builds still
    lower to the box pair (x2_producer use_constexact=False),
    SmallGain-style."""
    concludes: Judgment
    e1: Term
    e2: Term
    op: str          # '<=', '<', '=', '>=', '>'


@dataclass(frozen=True)
class PLiRPA(Proof):
    """lirpa (wire tag 16; Lean PLiRPAData).  Given box premises
    a <= preact <= b (literal shapes: (const a <= var) and
    (var <= const b)), a < 0 < b, and the six envelope side conditions,
    concludes the sandwich
        (beta + alpha*preact <= post) AND (post <= delta + gamma*preact)
    in Lean's pinned `lirpaConclusionForm` AST (affineWireTerm =
    TAdd(TConst(offset), TMul(TConst(slope), TVar(w)))).  Requires the
    port-lookup linkage reluLinked(H, preact, post)."""
    concludes: Judgment
    lower: Proof
    upper: Proof
    preact: str
    post: str
    a: object        # Rational, < 0
    b: object        # Rational, > 0
    alpha: object
    beta: object
    gamma: object
    delta: object


@dataclass(frozen=True)
class PReLUPos(Proof):
    """reluPos (wire tag 17; Lean PReLUPosData): from |- preact >= 0
    (literal .atom .ge (.var preact) (.const 0)) conclude
    |- post = preact.  Linkage-gated.  NOTE (the ge-premise gap, X2
    finding): the calculus derives <=-shaped facts (Farkas/Syzygy posts)
    and has no polarity flip, so the ge premise is only available where
    the hypothesis supplies it — e.g. inside the positive branch of the
    packaged sp-fact's disjunction, where `post = preact` is already a
    context atom.  Inhabited + battery-tested; the ACAS emission
    therefore handles stable-positive neurons by branch-and-prune
    instead."""
    concludes: Judgment
    premise: Proof
    preact: str
    post: str


@dataclass(frozen=True)
class PReLUNeg(Proof):
    """reluNeg (wire tag 18; Lean PReLUNegData): from |- preact <= 0
    (literal .atom .le (.var preact) (.const 0)) conclude |- post = 0.
    Linkage-gated.  The stable-off workhorse of the X2 emission."""
    concludes: Judgment
    premise: Proof
    preact: str
    post: str


@dataclass(frozen=True)
class PReLUNN(Proof):
    """reluNN (wire tag 19; Lean PReLUNNData): premise-free
    |- post >= 0.  Linkage-gated."""
    concludes: Judgment
    preact: str
    post: str


@dataclass(frozen=True)
class PReLUAbove(Proof):
    """reluAbove (wire tag 20; Lean PReLUAboveData): premise-free
    |- post >= preact.  Linkage-gated."""
    concludes: Judgment
    preact: str
    post: str


@dataclass(frozen=True)
class PReluUnfold(Proof):
    """Unfold-on-demand — Obligation U of the conservative-extension
    memo (sec 2), delta-reduction for hypernets, realized as a proof
    rule (this is the X2 seating BINARY.md sec 5.2 points at; no wire
    tag yet — the wire realization waits for the first producer that
    emits it).

    From a premise over the SAME hypothesis EXTENDED with the packaged
    node's expansion sp-facts on fresh internal wires, conclude the
    original sequent:

        premise:   Gamma AND EXP(preact, post, fresh)  |-  Psi
        concludes: Gamma                               |-  Psi

    where EXP = relu_expansion_spfacts (checker-recomputed, never
    carried).  Side conditions: reluLinked(H, preact, post); fresh
    pairwise-distinct, disjoint from H's wires and from the free wires
    of Gamma and Psi.  Soundness warrant: `relu_expansion_complete`
    (ReluExpansion.lean, the exists-direction of the projection lemma)
    — every model of Gamma extends to the fresh wires satisfying EXP,
    and Psi mentions no fresh wire."""
    concludes: Judgment
    premise: Proof
    preact: str
    post: str
    fresh: tuple     # RELU_UNFOLD_ARITY distinct new wire names


HOLE = "_hole"


def apply_predicate(predicate: Formula, arg: Term) -> Formula:
    """geolog's applyPredicateToTerm: substitute the placeholder wire."""
    return formula_subst(predicate, HOLE, arg)


# =========================================================================
# THROWAWAY serialization (real format = bernfmt)
# =========================================================================

def dump_repr(obj, path: str, header_note: str):
    """THROWAWAY inspection dump — plain pretty-repr, NOT the wire format.
    The real serialization is bernfmt (paper sec:wireformat Level 1)."""
    import pprint
    with open(path, "w") as fh:
        fh.write("# THROWAWAY inspection dump - real format = bernfmt\n")
        fh.write(f"# {header_note}\n")
        fh.write(pprint.pformat(obj, width=100))
        fh.write("\n")


# =========================================================================
# family-v1 (2026-07-17): the certificate-family objects
# BINARY.md SS6.1 blocklattice (0x40) / famJudgment (0x31), SS6.2 tag 27.
# Lean mirror: CertifiedBlockLattice / PProductLatticeData
# (lean/qtsl/Qtsl/ProductLattice.lean).
# =========================================================================

@dataclass(frozen=True)
class FamBlock:
    """One stored generator block: a nonempty proper cell-set (frozenset of
    row-major cell indices) + facet proofs aligned 1:1 with the CANONICAL
    boundary-facet list (BINARY.md SS6.1: sorted by (cell row-major index,
    axis, direction with - before +); grid-boundary facets owe nothing and
    are absent from the list)."""
    cells: frozenset          # frozenset[int]
    facet_proofs: tuple       # tuple[Proof, ...]


@dataclass(frozen=True)
class BlockLattice:
    """The wire family object (0x40): per-axis (wire, drift term,
    gridlines), stored generator blocks. The denoted lattice = closure of
    the stored blocks under bitmap-or/and, plus the implicit empty member
    and the whole arena; join/meet are never stored (BINARY.md SS6.1 —
    the recompute posture)."""
    axes: tuple               # tuple[(wire: str, drift: Term, gridlines: tuple[Rational,...]), ...]

    blocks: tuple             # tuple[FamBlock, ...]

    @property
    def amb_dim(self):
        return len(self.axes)

    @property
    def cells_per_axis(self):
        return tuple(len(g) - 1 for (_, _, g) in self.axes)

    @property
    def n_cells(self):
        n = 1
        for c in self.cells_per_axis:
            n *= c
        return n

    def cell_coords(self, idx: int) -> tuple:
        """Row-major, axis 0 slowest (BINARY.md SS6.1 / SS4 C order)."""
        cs = self.cells_per_axis
        out = [0] * len(cs)
        for i in range(len(cs) - 1, -1, -1):
            out[i] = idx % cs[i]
            idx //= cs[i]
        return tuple(out)

    def cell_index(self, coords) -> int:
        cs = self.cells_per_axis
        idx = 0
        for i in range(len(cs)):
            idx = idx * cs[i] + coords[i]
        return idx

    def cell_interval(self, coords, axis: int):
        g = self.axes[axis][2]
        return (g[coords[axis]], g[coords[axis] + 1])

    def arena_interval(self, axis: int):
        g = self.axes[axis][2]
        return (g[0], g[-1])

    def boundary_facets(self, cells: frozenset) -> tuple:
        """Canonical boundary cell-facet list for a cell-set: entries
        (cell_idx, axis, direction) with direction -1 (lower face; the
        block sits on the + side) or +1 (upper face; block on the - side).
        Facets on the grid boundary are EXCLUDED (the arena owes nothing).
        Order: (cell row-major index, axis, direction with - before +)."""
        out = []
        cs = self.cells_per_axis
        for idx in sorted(cells):
            co = self.cell_coords(idx)
            for axis in range(len(cs)):
                for d in (-1, 1):
                    nb = list(co)
                    nb[axis] += d
                    if nb[axis] < 0 or nb[axis] >= cs[axis]:
                        continue  # grid boundary: owes nothing
                    if self.cell_index(tuple(nb)) not in cells:
                        out.append((idx, axis, d))
        return tuple(out)

    def facet_pinned_value(self, facet):
        idx, axis, d = facet
        co = self.cell_coords(idx)
        g = self.axes[axis][2]
        return g[co[axis]] if d == -1 else g[co[axis] + 1]


@dataclass(frozen=True)
class FamJudgment:
    """The family judgment kind (0x31): 'lattice is a certified
    attracting-block lattice over its declared axes' — arena forward
    invariance DECLARED, not certified (BINARY.md SS6.1/SS6.2)."""
    lattice: BlockLattice


@dataclass(frozen=True)
class PProductLattice(Proof):
    """Node tag 27 (family-v1). concludes is a FamJudgment (the SS6.3
    family-root form), whose lattice must be `composite`. flows_only is
    published metadata (theta posture): zero proof weight; licenses the
    positioning documents' completeness citation for flow factors."""
    concludes: FamJudgment
    left: BlockLattice
    right: BlockLattice
    composite: BlockLattice
    flows_only: bool


def subst_tree(t: Term, wire: str, value) -> Term:
    """Pure tree substitution TVar(wire) -> TConst(value); no
    simplification (the [F2] rule-2 canonical form is the substituted
    TREE, structural equality)."""
    v = Rational(value)
    if isinstance(t, TVar):
        return TConst(v) if t.wire == wire else t
    if isinstance(t, TConst):
        return t
    if isinstance(t, TAdd):
        return TAdd(subst_tree(t.l, wire, v), subst_tree(t.r, wire, v))
    if isinstance(t, TMul):
        return TMul(subst_tree(t.l, wire, v), subst_tree(t.r, wire, v))
    if isinstance(t, TSub):
        return TSub(subst_tree(t.l, wire, v), subst_tree(t.r, wire, v))
    if isinstance(t, TNeg):
        return TNeg(subst_tree(t.t, wire, v))
    if isinstance(t, TIdx):
        return TIdx(subst_tree(t.t, wire, v), t.i)
    raise TypeError(f"subst_tree: unsupported term {t!r}")


def product_lattice_blocks(left: BlockLattice, right: BlockLattice):
    """[F5]'s extended-product generator enumeration: {b1 x b2 : b1 in
    left.blocks + [D1], b2 in right.blocks + [D2]} minus the implicit
    D1 x D2, in lex order (left-major, each factor's stored blocks first,
    its arena D last). Returns cell-sets over the composite grid (axes =
    left's then right's); facet proofs are NOT constructed here (the
    producer cites; the checker recomputes obligations)."""
    n_r_total = 1
    for c in right.cells_per_axis:
        n_r_total *= c
    left_all = [b.cells for b in left.blocks] + [frozenset(range(left.n_cells))]
    right_all = [b.cells for b in right.blocks] + [frozenset(range(right.n_cells))]
    out = []
    for i1, c1 in enumerate(left_all):
        for i2, c2 in enumerate(right_all):
            if i1 == len(left_all) - 1 and i2 == len(right_all) - 1:
                continue  # D1 x D2 = the composite arena, implicit
            cells = frozenset(a * n_r_total + b for a in c1 for b in c2)
            out.append(cells)
    return tuple(out)


# =========================================================================
# enclosure-v1 (catalogue flip, 2026-07-17):
# the remainder-bound rule, admissible tier.
# BINARY.md SS6.1 encJudgment (0x32), SS6.2 tag 28.
# Kernel mirrors: lean/qtsl-aux/QtslAux/Enclosure.lean
# (EncWitness / encCheck / encCheck_sound); hol/checker/bern_enclosureScript.sml.
# =========================================================================

ENC_FUNCS = ("exp", "sin", "cos")  # wire func_tag order: 0=exp 1=sin 2=cos


@dataclass(frozen=True)
class EncJudgment:
    """The remainder-bound judgment kind (0x32): 'for all x with |x| <= r,
    |func(x) - sum_{k<=n} a_k x^k| <= R', a_k the tag's exact Maclaurin
    coefficients (NOT serialized -- determined by (func, n); the checker
    recomputes them, BINARY.md recompute pattern). Meaning theorem:
    encCheck_sound, both towers."""
    func: str                 # "exp" | "sin" | "cos"
    n: int                    # truncation degree, inclusive
    r: Rational               # radius, 0 <= r < n+2 (checked, not assumed)
    R: Rational               # remainder cap, tail(n, r) <= R (checked)


@dataclass(frozen=True)
class PEnclosure(Proof):
    """Node tag 28 (enclosure-v1). A LEAF: no premises, no rule-specific
    payload -- concludes carries the whole witness. Only legal at root
    (BINARY.md SS6.3 enclosure-root profile)."""
    concludes: EncJudgment


# =========================================================================
# jet-v1 (2026-07-18): the PDE doctrine's jet layer as theory
# content. Contract: the upstream jet-v1 revision contract
# (vocabulary SS1, staged axioms SS2, checker obligations SS3).
# The wire target is the GeologMeta meta-schema (theory JetCalculus,
# substrate/theories/BLJet.rows.txt) -- NOT bernfmt, which was deprecated
# 2026-07-18, before any jet tag was minted (contract SS7).
# =========================================================================


@dataclass(frozen=True)
class JetFrame:
    """The pinned jet-coordinate family: wires[j] denotes d_x^j u (a
    family of SCALAR exact-Q wires; contract SS1.1's departure note).
    Frame WF ([J0]) is a checker obligation, not assumed here."""
    wires: tuple              # tuple[str, ...], len >= 1


@dataclass(frozen=True)
class JDiv:
    """Jet-judgment kind: int_T p(u_0(x),...,u_k(x)) dx = 0 for every
    sufficiently smooth T-periodic u -- warranted by p in im(D_x)
    (the PJetDiv witness) + rung lemma L2 (FTC on the circle)."""
    frame: JetFrame
    p: Term


@dataclass(frozen=True)
class JEvo:
    """Jet-judgment kind: d/dt int_T e dx = int_T g dx along classical
    solutions of u_t = chart -- rung lemma L1."""
    frame: JetFrame
    g: Term
    e: Term
    chart: Term


@dataclass(frozen=True)
class PJetDiv(Proof):
    """R2, the divergence/syzygy layer (doctrine SS1.2). Witness: the
    flux F; the checker recomputes D_x F and compares to concludes.p
    coefficientwise ([J1]). Root-only in jet-v1 (nothing consumes a
    jet judgment as a premise -- structural conservativity)."""
    concludes: JDiv
    flux: Term


@dataclass(frozen=True)
class PFunctionalDeriv(Proof):
    """R1, the evolution-integrand compile. A LEAF: the judgment carries
    (g, e, chart); the check IS the recompute
    g = sum_j de/du_j * D_x^j(chart) ([J2]). Root-only in jet-v1."""
    concludes: JEvo


@dataclass(frozen=True)
class PIntMono(Proof):
    """L3, pointwise-cone => integral row -- the one sequent-fragment
    addition (PSyzygy consumes its conclusion natively). premise proves
    pre |- (l <= 0) with poly(l) = -poly(integrand); the conclusion is
    pre |- (l' <= 0) with poly(l') = -x_{int_wire}, binding the
    DECLARED denotation int_wire = int_T integrand(jet u(x)) dx as
    manifest certificate data ([J3]; soundness under the box-confinement
    hypotheses carried in pre -- rung lemma L3)."""
    concludes: Judgment
    premise: Proof
    int_wire: str
    integrand: Term
    frame: JetFrame
