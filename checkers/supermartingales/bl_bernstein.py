"""Exact-Q Bernstein-coefficient machinery for Bernstein Logic (lane F1).

Implements, over exact rationals (SymPy), the arithmetic core that the
BernCone rule's side-condition needs (upstream design paper, not included in this repository:
sec:gen-bern-setup / sec:gen-bern-rule-statement):

  * barycentric coordinate functions of a rational n-simplex,
  * monomial -> degree-d Bernstein basis change on a simplex,
  * degree elevation of Bernstein coefficient families,
  * inward-layer polynomials q_k and forward-difference polynomials P_j
    on the core face F_S for an extension set S,
  * the full (j, gamma) grid check `berncone_check` (the rule's final
    premise: every degree-d Bernstein coefficient of every P_j satisfies P).

Everything is symbolic/exact; floats never appear.  This module is the
SymPy/exact-Q oracle at the top of the BUILD-PLAN 5.3 proptest chain.

Conventions (paper sec:gen-bern-setup, verified against the paper's (star)
identity by `selftest_star_identity` below — run via selftest_all()):

  * A simplex is a tuple of n+1 affinely-independent vertices in Q^n.
  * Multi-indices alpha over vertex set {0..n} with |alpha| = d index
    Bernstein coefficients: p(x) = sum_alpha b_alpha * multinom(d, alpha)
    * prod_i lambda_i(x)^alpha_i.
  * S is a proper subset of {0..n} ("extended indices"); Sbar the rest.
  * q_k (k in N^S, |k| <= d) is the Bernstein polynomial on F_S of degree
    d - |k| with coefficients b_{(k, beta)}.
  * P_j = sum_{k <= j} (-1)^{|k|} prod_i binom(j_i, k_i) q_k, degree-
    elevated to common degree d on F_S.
"""

from __future__ import annotations

from itertools import product as _cartesian
from functools import lru_cache

import sympy as sp
from sympy import Rational, binomial, factorial, prod, symbols


# ---------------------------------------------------------------------------
# multi-index helpers
# ---------------------------------------------------------------------------

def multi_indices(num_slots: int, total: int):
    """All tuples alpha in N^num_slots with |alpha| = total."""
    if num_slots == 0:
        return [()] if total == 0 else []
    out = []
    for first in range(total + 1):
        for rest in multi_indices(num_slots - 1, total - first):
            out.append((first,) + rest)
    return out


def multi_indices_upto(num_slots: int, total: int):
    """All tuples alpha in N^num_slots with |alpha| <= total."""
    out = []
    for t in range(total + 1):
        out.extend(multi_indices(num_slots, t))
    return out


def multinom(d: int, alpha) -> sp.Integer:
    """Multinomial coefficient d! / prod(alpha_i!), requiring sum(alpha) == d."""
    assert sum(alpha) == d, (d, alpha)
    return factorial(d) // prod([factorial(a) for a in alpha])


# ---------------------------------------------------------------------------
# simplices and barycentric coordinates
# ---------------------------------------------------------------------------

def barycentric_coords(vertices, xs):
    """Affine barycentric coordinate functions lambda_0..lambda_n of a simplex.

    vertices: sequence of n+1 points, each a sequence of n Rationals.
    xs: n sympy symbols for the ambient coordinates.
    Returns [lambda_0(x), ..., lambda_n(x)] as sympy expressions, exact.
    Raises ValueError on a degenerate simplex (this is a checker-side
    well-formedness condition: mutation battery class 'corrupted simplex').
    """
    n = len(xs)
    if len(vertices) != n + 1:
        raise ValueError(f"need {n + 1} vertices for an {n}-simplex, got {len(vertices)}")
    # Solve  [V^T; 1..1] * lam = [x; 1]  for lam.
    A = sp.Matrix([[Rational(vertices[j][i]) for j in range(n + 1)] for i in range(n)]
                  + [[1] * (n + 1)])
    if A.det() == 0:
        raise ValueError(f"degenerate simplex: vertices {vertices}")
    rhs = sp.Matrix(list(xs) + [1])
    lam = A.solve(rhs)
    return [sp.expand(lam[i]) for i in range(n + 1)]


def bernstein_coeffs(poly_expr, xs, vertices, d):
    """Degree-d Bernstein coefficients of poly_expr on the simplex `vertices`.

    Returns dict {alpha: b_alpha} over |alpha| = d, alpha in N^{n+1}, exact.
    Raises ValueError if deg(poly_expr) > d (the 'off-by-one degree' mutant
    class must be caught here, not silently truncated).

    Method: substitute the vertex-form parametrization x = sum_i lam_i * V_i
    with sum lam = 1 eliminated via lam_n = 1 - sum_{i<n} lam_i, then
    homogenize back.  Equivalent, cleaner exact route: evaluate the
    coefficients via the standard formula through the monomial basis on the
    reference simplex.  We take the direct route: express p in the lambda
    variables (exactly), homogenize to total degree d using (sum lam = 1),
    and divide by multinomial weights.
    """
    n = len(xs)
    poly = sp.Poly(sp.expand(poly_expr), *xs) if xs else None
    if xs:
        if poly.total_degree() > d:
            raise ValueError(
                f"polynomial degree {poly.total_degree()} exceeds claimed d={d}")
    lams = list(symbols(f"lam0:{n + 1}", positive=False))
    # x_i = sum_j lam_j * (V_j)_i
    subs = {xs[i]: sum(lams[j] * Rational(vertices[j][i]) for j in range(n + 1))
            for i in range(n)}
    p_lam = sp.expand(poly_expr.subs(subs))
    # homogenize each monomial of degree e <= d by multiplying (sum lam)^(d-e)
    total = sp.Integer(0)
    p_poly = sp.Poly(p_lam, *lams)
    one = sum(lams)
    for monom, coeff in p_poly.terms():
        e = sum(monom)
        assert e <= d
        total += coeff * prod([lams[i] ** monom[i] for i in range(n + 1)]) * one ** (d - e)
    total = sp.expand(total)
    hom = sp.Poly(total, *lams)
    out = {}
    for alpha in multi_indices(n + 1, d):
        c = hom.coeff_monomial(prod([lams[i] ** alpha[i] for i in range(n + 1)]))
        # NB: bare sp.nsimplify is FORBIDDEN on exact values — without
        # rational=True it runs a numeric search that can replace an exact
        # Rational by a numerically-close radical expression (witness, sympy
        # 1.14.0: nsimplify(Rational(1679, 12)) == 35*2**(260/269)*3**(495/538)
        # *5**(61/269)*7**(425/538)/9 — caught by the triple differential
        # harness, 2026-07-16). c is exact by construction; divide directly.
        out[alpha] = sp.simplify(c / multinom(d, alpha))
    return out


def eval_bernstein(coeffs, d, lams):
    """Evaluate sum_alpha b_alpha * multinom(d,alpha) * lam^alpha symbolically."""
    return sp.expand(sum(
        coeffs[alpha] * multinom(d, alpha) * prod([lams[i] ** alpha[i] for i in range(len(alpha))])
        for alpha in coeffs))


# ---------------------------------------------------------------------------
# degree elevation (on any simplex, coefficients indexed by multi-indices)
# ---------------------------------------------------------------------------

def elevate_once(coeffs, e):
    """Elevate a degree-e Bernstein coefficient family to degree e+1.

    Standard identity: c'_beta = sum_i (beta_i / (e+1)) * c_{beta - e_i}.
    Works for coefficients valued in any Q-vector space (here: sympy exprs).
    """
    slots = len(next(iter(coeffs)))
    out = {}
    for beta in multi_indices(slots, e + 1):
        acc = sp.Integer(0)
        for i in range(slots):
            if beta[i] > 0:
                lower = beta[:i] + (beta[i] - 1,) + beta[i + 1:]
                acc += Rational(beta[i], e + 1) * coeffs[lower]
        out[beta] = sp.expand(acc)
    return out


def elevate_to(coeffs, e, target):
    """Elevate a degree-e family to degree `target` >= e."""
    cur, ce = coeffs, e
    while ce < target:
        cur = elevate_once(cur, ce)
        ce += 1
    return cur


# ---------------------------------------------------------------------------
# extension sets: q_k, P_j, and the BernCone grid check
# ---------------------------------------------------------------------------

def inward_layer_qk(b, d, S, k):
    """Coefficients of q_k on F_S (degree d - |k|), from the full family b.

    b: {alpha in N^{n+1}, |alpha| = d} -> value.  S: sorted tuple of extended
    indices.  k: tuple over S (aligned with sorted S), |k| <= d.
    Returns {beta over Sbar: b_{(k, beta)}} with |beta| = d - |k|.
    """
    npl1 = len(next(iter(b)))
    Sbar = [i for i in range(npl1) if i not in S]
    out = {}
    for beta in multi_indices(len(Sbar), d - sum(k)):
        alpha = [0] * npl1
        for pos, i in enumerate(sorted(S)):
            alpha[i] = k[pos]
        for pos, i in enumerate(Sbar):
            alpha[i] = beta[pos]
        out[beta] = b[tuple(alpha)]
    return out


def forward_diff_Pj(b, d, S, j):
    """Degree-d Bernstein coefficients (on F_S) of the forward-difference P_j.

    P_j := sum_{k <= j} (-1)^{|k|} * prod_i binom(j_i, k_i) * q_k,
    with each q_k (degree d - |k|) degree-elevated to d on F_S first.
    Returns {gamma over Sbar, |gamma| = d: coefficient}.
    """
    Ssorted = sorted(S)
    npl1 = len(next(iter(b)))
    Sbar = [i for i in range(npl1) if i not in S]
    acc = {gamma: sp.Integer(0) for gamma in multi_indices(len(Sbar), d)}
    for k in _cartesian(*[range(ji + 1) for ji in j]):
        sign = (-1) ** sum(k)
        w = prod([binomial(j[pos], k[pos]) for pos in range(len(j))])
        qk = inward_layer_qk(b, d, tuple(Ssorted), k)
        qk_d = elevate_to(qk, d - sum(k), d)
        for gamma in acc:
            acc[gamma] += sign * w * qk_d[gamma]
    return {gamma: sp.expand(v) for gamma, v in acc.items()}


def berncone_grid(b, d, S):
    """The full BernCone (j, gamma) grid: {j: {gamma: coefficient}}.

    j ranges over N^S with |j| <= d; for S = (), the single j = () gives back
    the plain coefficient family (P_() = q_() = b), i.e. classical Bernstein.
    """
    Ssorted = tuple(sorted(S))
    out = {}
    for j in multi_indices_upto(len(Ssorted), d):
        out[j] = forward_diff_Pj(b, d, Ssorted, j)
    return out


def berncone_check(vertices, xs, S, d, poly_expr, predicate):
    """The BernCone side-condition, exact: every degree-d Bernstein coefficient
    of every P_j on F_S satisfies `predicate` (a callable Expr -> bool that
    must decide exactly, e.g. lambda w: sp.ask/relational evaluation on Q).

    Returns (ok: bool, failures: list of (j, gamma, value)).
    """
    b = bernstein_coeffs(poly_expr, xs, vertices, d)
    grid = berncone_grid(b, d, tuple(sorted(S)))
    failures = []
    for j, fam in grid.items():
        for gamma, val in fam.items():
            if not predicate(val):
                failures.append((j, gamma, val))
    return (not failures), failures


# ---------------------------------------------------------------------------
# self-tests: the paper's (star) identity and classical sanity checks
# ---------------------------------------------------------------------------

def selftest_star_identity(n, S, d, verbose=False):
    """Symbolically verify the boxed identity (star) of thm:berncone-sound:

        p(x(u, y)) == sum_{|j| <= d} multinom(d; |j|, d-|j|) * multinom(|j|; j)
                      * u^j * P_j(y)

    with FREE symbolic Bernstein coefficients b_alpha, on the parametrization
    lambda_i = -u_i (i in S), lambda_i = (1+U) * mu_i (i in Sbar).
    This is a genuine symbolic proof for the given (n, S, d), and it pins the
    sign conventions of q_k / P_j (the recorded-bug class: sign-direction
    errors in exactly this machinery — review lane 4).
    """
    S = tuple(sorted(S))
    npl1 = n + 1
    Sbar = [i for i in range(npl1) if i not in S]
    assert len(S) < npl1, "S must be a proper subset"
    b = {alpha: sp.Symbol(f"b_{'_'.join(map(str, alpha))}")
         for alpha in multi_indices(npl1, d)}
    us = {i: sp.Symbol(f"u{i}", nonnegative=True) for i in S}
    mus = {i: sp.Symbol(f"mu{i}") for i in Sbar}
    U = sum(us.values())
    # lambda substitution per Step 1 of the soundness proof
    lam = {}
    for i in range(npl1):
        lam[i] = -us[i] if i in S else (1 + U) * mus[i]
    lhs = sum(b[alpha] * multinom(d, alpha) * prod([lam[i] ** alpha[i] for i in range(npl1)])
              for alpha in b)
    rhs = sp.Integer(0)
    grid = berncone_grid(b, d, S)
    for j, fam in grid.items():
        jt = sum(j)
        pref = (factorial(d) // (factorial(jt) * factorial(d - jt))) * multinom(jt, j)
        uj = prod([us[Si] ** j[pos] for pos, Si in enumerate(S)])
        Pj_y = sum(fam[gamma] * multinom(d, gamma)
                   * prod([mus[Sbar[pos]] ** gamma[pos] for pos in range(len(Sbar))])
                   for gamma in fam)
        rhs += pref * uj * Pj_y
    # impose sum_{i in Sbar} mu_i = 1 by eliminating the last mu
    last = Sbar[-1]
    elim = {mus[last]: 1 - sum(mus[i] for i in Sbar[:-1])}
    diff = sp.expand((lhs - rhs).subs(elim))
    ok = diff == 0
    if verbose:
        print(f"  (star) identity n={n} S={S} d={d}: {'OK' if ok else 'FAIL ' + str(diff)}")
    return ok


def selftest_classical(verbose=False):
    """Classical Bernstein sanity: on conv(1,2) in 1D at d=1, coefficients of
    1/2 + 2x are the endpoint values 5/2 and 9/2 (the paper's branch-B numbers,
    sec:example-proof)."""
    x = sp.Symbol("x")
    coeffs = bernstein_coeffs(Rational(1, 2) + 2 * x, (x,), [(1,), (2,)], 1)
    expect = {(1, 0): Rational(5, 2), (0, 1): Rational(9, 2)}
    ok = coeffs == expect
    if verbose:
        print(f"  classical [1,2] d=1 endpoint coefficients: "
              f"{'OK' if ok else f'FAIL {coeffs} != {expect}'}")
    return ok


def selftest_convex_hull(verbose=False):
    """Bernstein convex-hull property spot-check: values of p on the simplex
    lie within [min, max] of the coefficients (exercised on a 2D quadratic,
    exact rational sample points)."""
    x, y = symbols("x y")
    verts = [(0, 0), (1, 0), (0, 1)]
    p = x ** 2 + x * y - y + Rational(1, 3)
    d = 2
    coeffs = bernstein_coeffs(p, (x, y), verts, d)
    lo = min(coeffs.values())
    hi = max(coeffs.values())
    ok = True
    for (px, py) in [(0, 0), (1, 0), (0, 1), (Rational(1, 3), Rational(1, 3)),
                     (Rational(1, 2), Rational(1, 4))]:
        v = p.subs({x: px, y: py})
        ok = ok and (lo <= v <= hi)
    if verbose:
        print(f"  convex-hull enclosure on 2D quadratic: {'OK' if ok else 'FAIL'}")
    return ok


def selftest_all(verbose=True):
    results = {
        "classical_paper_branchB": selftest_classical(verbose),
        "convex_hull_2d": selftest_convex_hull(verbose),
        # (star) identity across shapes: 1D apex, 2D one-facet, 2D two-facet,
        # 3D mixed — each a symbolic proof instance with free coefficients.
        "star_n1_S0_d2": selftest_star_identity(1, (0,), 2, verbose),
        "star_n2_S0_d2": selftest_star_identity(2, (0,), 2, verbose),
        "star_n2_S01_d2": selftest_star_identity(2, (0, 1), 2, verbose),
        "star_n2_S1_d3": selftest_star_identity(2, (1,), 3, verbose),
        "star_n3_S12_d2": selftest_star_identity(3, (1, 2), 2, verbose),
    }
    return results


if __name__ == "__main__":
    res = selftest_all(verbose=True)
    bad = [k for k, v in res.items() if not v]
    print("ALL OK" if not bad else f"FAILURES: {bad}")
    raise SystemExit(0 if not bad else 1)
