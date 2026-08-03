import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-! # The bounded-generator fence transport theorem

Soundness of the transposed Lyapunov drift row for open quantum systems
at the finite-dimensional stratum — where every generator is bounded and
the semigroup is uniformly continuous, so the argument reduces to
semigroup differentiation plus Grönwall. Prose source theorem:
Emzir–Woolley–Petersen, *Stability Analysis of Quantum Systems: a
Lyapunov Criterion and an Invariance Principle* (Automatica 146, 2022),
Theorem `thm:LyapunovStability`, clause 3 (global exponential
stability), whose proof for uniformly continuous semigroups is exactly
what is mechanized here.

**What is proved** (why the finite-dimensional fence is *sufficient* for
the transposed drift row
$\mathcal{L}^\dagger(V) \preceq -\gamma V + \zeta\mathbb{1}$ to be sound):

* `trace_mul_nonneg` — Born-pairing positivity: $\rho, M \succeq 0 \Rightarrow
  \operatorname{tr}(\rho M) \ge 0$ (via CFC square root + congruence + cyclicity);
* `re_trace_mul_le_of_le` / `re_trace_drift_le` — the Loewner-monotone pairing
  step: the certificate's PSD drift row $W \preceq -\gamma V + \zeta\mathbb{1}$
  yields the scalar differential inequality against any state;
* `exp_contraction_of_deriv_le` — the sharp scalar Grönwall step,
  $x' \le -\gamma x + \zeta \Rightarrow x(t) \le (x(0) - \zeta/\gamma)
  e^{-\gamma t} + \zeta/\gamma$
  (via `le_gronwallBound_of_liminf_deriv_right_le`, kept sharp
  rather than relaxed — the source display exactly);
* `trace_eq_of_flow` — trace conservation along any global solution of a
  trace-annihilating generator (so unit trace is a *theorem* of the GKSL form
  below, not a hypothesis about the flow);
* `fence_transport` — **the transport theorem**: for any $C^1$ solution of the
  master equation $\dot\rho = \mathcal{L}(\rho)$ with $\mathcal{L}$
  trace-annihilating, positivity of the flow on $[0,b]$ (the CP residual — see
  below), unit initial trace, and the drift row on the Heisenberg image $W =
  \mathcal{L}^\dagger(V)$, the expected Lyapunov observable obeys the exponential
  bound $\operatorname{tr}(V\rho_t) \le (\operatorname{tr}(V\rho_0) -
  \zeta/\gamma)e^{-\gamma t} + \zeta/\gamma$;
* `gamma_mul_re_trace_le_zeta_of_invariant` — the normalization receipt: at any
  invariant state, the drift row forces $\gamma v_0 \le \zeta$ (one direction of
  the normalization $\zeta = \gamma v_0$ that the stability theorem's two
  clauses jointly force; the other direction is the tightness *choice*, design
  content, not a theorem);
* `gksl`/`gkslDag` + `gksl_trace_eq_zero` + `gksl_pairing` — the concrete GKSL
  (Gorini–Kossakowski–Sudarshan–Lindblad) generator as a linear endomorphism, its
  trace-annihilation (discharging `hann` for every GKSL mechanism profile), and
  the Schrödinger↔Heisenberg trace adjunction (discharging `hpair`, and
  *computing* the Heisenberg image the drift row is stated against).

**The priced residual (deliberate, named)**: positivity preservation of the GKSL
flow — complete positivity of $e^{t\mathcal{L}}$ (Lindblad 1976) — enters
`fence_transport` as the hypothesis `hpsd`, not as a theorem; a certificate
ships the PSD witness of the drift row, which this file consumes as `hrow`.
Solution existence for the fence stratum (linear ODE in finite dimension) is
likewise textbook and quantified over here (`hflow` takes *any* solution)
rather than constructed. -- [classical]
-/

open Set Filter Topology Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise

namespace Qtsl

namespace OpenQuantum

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## Born-pairing positivity and the Loewner-monotone pairing step -/

/-- Trace pairing of positive semidefinite matrices is nonnegative (in the scoped
`ComplexOrder`): the Born-rule positivity that lets the drift row's PSD witness
act on states. Route: `M = √M · √M` (CFC square root), cyclicity of the trace,
and congruence-invariance of positive semidefiniteness. -/
theorem trace_mul_nonneg {ρ M : Matrix d d ℂ} (hρ : ρ.PosSemidef) (hM : M.PosSemidef) :
    0 ≤ (ρ * M).trace := by
  have hM0 : (0 : Matrix d d ℂ) ≤ M := hM.nonneg
  have hs0 : (0 : Matrix d d ℂ) ≤ CFC.sqrt M := CFC.sqrt_nonneg M
  have hss : CFC.sqrt M * CFC.sqrt M = M := CFC.sqrt_mul_sqrt_self M hM0
  have hsH : (CFC.sqrt M)ᴴ = CFC.sqrt M := by
    have h := IsSelfAdjoint.of_nonneg hs0
    rwa [IsSelfAdjoint, star_eq_conjTranspose] at h
  have hcong : ((CFC.sqrt M)ᴴ * ρ * CFC.sqrt M).PosSemidef :=
    hρ.conjTranspose_mul_mul_same (CFC.sqrt M)
  rw [hsH] at hcong
  have htr : (CFC.sqrt M * ρ * CFC.sqrt M).trace = (ρ * M).trace := by
    rw [trace_mul_cycle, hss, trace_mul_comm]
  rw [← htr]
  exact hcong.trace_nonneg

/-- Monotonicity of the state pairing in the Loewner order: for a state `ρ` and
`A ≤ B` (scoped `MatrixOrder`), `re tr(ρA) ≤ re tr(ρB)`. -/
theorem re_trace_mul_le_of_le {ρ A B : Matrix d d ℂ} (hρ : ρ.PosSemidef) (hAB : A ≤ B) :
    ((ρ * A).trace).re ≤ ((ρ * B).trace).re := by
  have h0 : 0 ≤ (ρ * (B - A)).trace := trace_mul_nonneg hρ (Matrix.le_iff.mp hAB)
  have h1 := Complex.re_le_re h0
  rw [mul_sub, trace_sub, Complex.sub_re, Complex.zero_re] at h1
  linarith

/-- **The drift row acts on states**: if the certificate's operator inequality
`W ≤ (-γ) • V + ζ • 1` holds (its PSD witness is the shipped check), then against
any unit-trace state the scalar drift inequality
`re tr(ρW) ≤ -γ · re tr(ρV) + ζ` follows. This is the dictionary
"regions ↦ projections, evaluation ↦ trace pairing" cashed at the inequality
level. -/
theorem re_trace_drift_le {ρ V W : Matrix d d ℂ} {γ ζ : ℝ}
    (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1)
    (hrow : W ≤ (-γ : ℝ) • V + (ζ : ℝ) • (1 : Matrix d d ℂ)) :
    ((ρ * W).trace).re ≤ -γ * ((ρ * V).trace).re + ζ := by
  have h := re_trace_mul_le_of_le hρ hrow
  rw [mul_add, trace_add, mul_smul_comm, mul_smul_comm, trace_smul, trace_smul,
    mul_one, hρtr, Complex.add_re] at h
  rw [Complex.real_smul, Complex.real_smul, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul, Complex.one_re, mul_one] at h
  exact h

/-! ## The sharp scalar Grönwall step -/

/-- Sharp exponential-contraction Grönwall: a differentiable `x` with
`x' ≤ -γ x + ζ` on `[0, b)` satisfies
`x t ≤ (x 0 - ζ/γ) e^{-γ t} + ζ/γ` on `[0, b]`. Via
`le_gronwallBound_of_liminf_deriv_right_le` with `K = -γ`, `ε = ζ` — kept in the
sharp form (no sign condition on `ζ` is needed, unlike the relaxed
absorbing-ball form in `PdeDini.lean`). -/
theorem exp_contraction_of_deriv_le {x x' : ℝ → ℝ} {γ ζ b : ℝ} (hγ : 0 < γ)
    (hcont : ContinuousOn x (Icc 0 b))
    (hderiv : ∀ t ∈ Ico 0 b, HasDerivAt x (x' t) t)
    (hle : ∀ t ∈ Ico 0 b, x' t ≤ -γ * x t + ζ) :
    ∀ t ∈ Icc 0 b, x t ≤ (x 0 - ζ / γ) * Real.exp (-γ * t) + ζ / γ := by
  intro t ht
  have hfreq : ∀ s ∈ Ico 0 b, ∀ r, x' s < r →
      ∃ᶠ z in 𝓝[>] s, (z - s)⁻¹ * (x z - x s) < r := by
    intro s hs r hr
    have hsub : Ioi s ⊆ {s}ᶜ := fun z (hz : s < z) => hz.ne'
    have hslope : Tendsto (slope x s) (𝓝[>] s) (𝓝 (x' s)) :=
      ((hderiv s hs).tendsto_slope).mono_left (nhdsWithin_mono s hsub)
    refine ((hslope.eventually_lt_const hr).mono fun z hz => ?_).frequently
    rwa [slope_def_field, div_eq_inv_mul] at hz
  have h := le_gronwallBound_of_liminf_deriv_right_le (f := x) (f' := x')
    (δ := x 0) (K := -γ) (ε := ζ) (a := 0) (b := b) hcont hfreq le_rfl hle t ht
  rw [gronwallBound_of_K_ne_0 (neg_ne_zero.mpr hγ.ne'), sub_zero] at h
  refine h.trans_eq ?_
  rw [div_neg]
  ring

/-! ## Differentiating observable pairings along a matrix-valued curve -/

/-- Pairing against a fixed observable is a (finite-dimensional, hence
continuous) linear functional, so it commutes with differentiation along any
matrix-valued curve. -/
theorem hasDerivAt_trace_mul {ρ : ℝ → Matrix d d ℂ} {D : Matrix d d ℂ} {t : ℝ}
    (V : Matrix d d ℂ) (hρ : HasDerivAt ρ D t) :
    HasDerivAt (fun s => (ρ s * V).trace) ((D * V).trace) t := by
  classical
  let clm : Matrix d d ℂ →L[ℝ] ℂ :=
    (LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap d ℂ ℂ).comp (LinearMap.mulRight ℂ V))).restrictScalars ℝ
  have hc : HasDerivAt (fun s => clm (ρ s)) (clm D) t :=
    clm.hasFDerivAt.comp_hasDerivAt t hρ
  have he : ∀ A : Matrix d d ℂ, clm A = (A * V).trace := fun A => rfl
  simp only [he] at hc
  exact hc

/-- Real part of the observable pairing, differentiated along the curve. -/
theorem hasDerivAt_re_trace_mul {ρ : ℝ → Matrix d d ℂ} {D : Matrix d d ℂ} {t : ℝ}
    (V : Matrix d d ℂ) (hρ : HasDerivAt ρ D t) :
    HasDerivAt (fun s => ((ρ s * V).trace).re) (((D * V).trace).re) t := by
  have hc : HasDerivAt (fun s => Complex.reCLM ((ρ s * V).trace))
      (Complex.reCLM ((D * V).trace)) t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_trace_mul V hρ)
  exact hc

/-- **Trace conservation**: along any global solution of `ρ' = L(ρ)` with `L`
trace-annihilating (true of every GKSL-form generator, `gksl_trace_eq_zero`
below), the trace is constant. Unit trace is therefore inherited from the
initial condition, not hypothesized about the flow. -/
theorem trace_eq_of_flow {Lop : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ}
    {ρ : ℝ → Matrix d d ℂ}
    (hflow : ∀ t, HasDerivAt ρ (Lop (ρ t)) t)
    (hann : ∀ X, (Lop X).trace = 0) (t : ℝ) :
    (ρ t).trace = (ρ 0).trace := by
  have hD : ∀ s, HasDerivAt (fun u => (ρ u).trace) 0 s := by
    intro s
    have h := hasDerivAt_trace_mul (V := (1 : Matrix d d ℂ)) (hflow s)
    simp only [mul_one] at h
    simpa [hann] using h
  exact is_const_of_deriv_eq_zero (fun s => (hD s).differentiableAt)
    (fun s => (hD s).deriv) t 0

/-! ## The fence transport theorem -/

/-- **The bounded-generator fence transport theorem.** At the fence stratum —
finite-dimensional mechanisms, so every generator is bounded and the semigroup
is uniformly continuous — the transposed drift row is *sound*: for any `C¹`
solution `ρ` of the master equation with trace-annihilating generator, unit
initial trace, positive flow (`hpsd`, the CP residual — the one hypothesis
deliberately left undischarged; see the module docstring), and the
certificate's operator inequality `W ≤ (-γ)V + ζ·1` on the Heisenberg image
`W` of the Lyapunov observable `V` (`hpair`), the expected value obeys the
sharp exponential bound of Emzir–Woolley–Petersen Theorem
`thm:LyapunovStability`(3). -/
theorem fence_transport
    {Lop : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ} {ρ : ℝ → Matrix d d ℂ}
    {V W : Matrix d d ℂ} {γ ζ b : ℝ} (hγ : 0 < γ)
    (hflow : ∀ t, HasDerivAt ρ (Lop (ρ t)) t)
    (hpair : ∀ X, (Lop X * V).trace = (X * W).trace)
    (hann : ∀ X, (Lop X).trace = 0)
    (htr0 : (ρ 0).trace = 1)
    (hpsd : ∀ t ∈ Icc (0 : ℝ) b, (ρ t).PosSemidef)
    (hrow : W ≤ (-γ : ℝ) • V + (ζ : ℝ) • (1 : Matrix d d ℂ)) :
    ∀ t ∈ Icc (0 : ℝ) b,
      ((ρ t * V).trace).re ≤
        (((ρ 0 * V).trace).re - ζ / γ) * Real.exp (-γ * t) + ζ / γ := by
  have hxD : ∀ t, HasDerivAt (fun s => ((ρ s * V).trace).re)
      (((Lop (ρ t) * V).trace).re) t :=
    fun t => hasDerivAt_re_trace_mul V (hflow t)
  have hcont : ContinuousOn (fun s => ((ρ s * V).trace).re) (Icc 0 b) :=
    (continuous_iff_continuousAt.mpr fun t => (hxD t).continuousAt).continuousOn
  refine exp_contraction_of_deriv_le hγ hcont (fun t _ => hxD t) ?_
  intro t ht
  have htmem : t ∈ Icc (0 : ℝ) b := ⟨ht.1, ht.2.le⟩
  have h1 : ((Lop (ρ t) * V).trace).re = ((ρ t * W).trace).re := by rw [hpair]
  rw [h1]
  exact re_trace_drift_le (hpsd t htmem)
    ((trace_eq_of_flow hflow hann t).trans htr0) hrow

/-- **The normalization receipt** (one direction of the normalization
`ζ = γ v₀` that the stability theorem's two clauses jointly force): at any
invariant state `ρ⋆` (`L ρ⋆ = 0`), the drift row forces `γ · tr(V ρ⋆) ≤ ζ` —
stationarity leaves no room below `γ v₀`. The converse direction (choosing `ζ`
no larger than `γ v₀`) is the tightness *choice* the certificate normalization
records; it is design content, not a theorem. -/
theorem gamma_mul_re_trace_le_zeta_of_invariant
    {Lop : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ}
    {ρs V W : Matrix d d ℂ} {γ ζ : ℝ}
    (hstat : Lop ρs = 0)
    (hpair : ∀ X, (Lop X * V).trace = (X * W).trace)
    (hpsd : ρs.PosSemidef) (htr : ρs.trace = 1)
    (hrow : W ≤ (-γ : ℝ) • V + (ζ : ℝ) • (1 : Matrix d d ℂ)) :
    γ * ((ρs * V).trace).re ≤ ζ := by
  have h0 : (ρs * W).trace = 0 := by
    rw [← hpair, hstat, zero_mul, trace_zero]
  have h := re_trace_drift_le hpsd htr hrow
  rw [h0, Complex.zero_re] at h
  linarith

/-! ## The GKSL generator: trace-annihilation and the Heisenberg adjunction

The concrete mechanism-profile generator. `gksl_trace_eq_zero` discharges the
`hann` hypothesis of `fence_transport` for every GKSL profile;
`gksl_pairing` discharges `hpair` with the *computed* Heisenberg image
`gkslDag H L V`, so the drift row is stated against an explicit matrix the
PSD machinery can check. -/

section GKSL

variable {ι : Type*} [Fintype ι]

/-- The GKSL (Lindblad) generator in Schrödinger form, assembled from the
library's multiplication linear maps:
`gksl H L ρ = -i(Hρ - ρH) + Σᵢ (Lᵢ ρ Lᵢᴴ - ½(LᵢᴴLᵢ ρ + ρ LᵢᴴLᵢ))`. -/
noncomputable def gksl (H : Matrix d d ℂ) (L : ι → Matrix d d ℂ) :
    Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ :=
  (-Complex.I) • (LinearMap.mulLeft ℂ H - LinearMap.mulRight ℂ H) +
    ∑ i, ((LinearMap.mulRight ℂ (L i)ᴴ).comp (LinearMap.mulLeft ℂ (L i)) -
      (2⁻¹ : ℂ) • (LinearMap.mulLeft ℂ ((L i)ᴴ * L i) +
        LinearMap.mulRight ℂ ((L i)ᴴ * L i)))

/-- The GKSL generator in Heisenberg form (the adjoint under the trace pairing,
`gksl_pairing`): `gkslDag H L V = i(HV - VH) + Σᵢ (Lᵢᴴ V Lᵢ - ½(LᵢᴴLᵢ V + V LᵢᴴLᵢ))`. -/
noncomputable def gkslDag (H : Matrix d d ℂ) (L : ι → Matrix d d ℂ) :
    Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ :=
  Complex.I • (LinearMap.mulLeft ℂ H - LinearMap.mulRight ℂ H) +
    ∑ i, ((LinearMap.mulLeft ℂ (L i)ᴴ).comp (LinearMap.mulRight ℂ (L i)) -
      (2⁻¹ : ℂ) • (LinearMap.mulLeft ℂ ((L i)ᴴ * L i) +
        LinearMap.mulRight ℂ ((L i)ᴴ * L i)))

theorem gksl_apply (H : Matrix d d ℂ) (L : ι → Matrix d d ℂ) (X : Matrix d d ℂ) :
    gksl H L X = (-Complex.I) • (H * X - X * H) +
      ∑ i, (L i * X * (L i)ᴴ -
        (2⁻¹ : ℂ) • ((L i)ᴴ * L i * X + X * ((L i)ᴴ * L i))) := by
  simp [gksl, mul_assoc]

theorem gkslDag_apply (H : Matrix d d ℂ) (L : ι → Matrix d d ℂ) (V : Matrix d d ℂ) :
    gkslDag H L V = Complex.I • (H * V - V * H) +
      ∑ i, ((L i)ᴴ * V * L i -
        (2⁻¹ : ℂ) • ((L i)ᴴ * L i * V + V * ((L i)ᴴ * L i))) := by
  simp [gkslDag, mul_assoc]

/-- **Trace-annihilation of the GKSL form** — an algebraic identity of the form
itself (no hypotheses on `H` or the `Lᵢ`): commutators and the dissipator both
vanish under the trace by cyclicity. Discharges `hann` in `fence_transport`. -/
theorem gksl_trace_eq_zero (H : Matrix d d ℂ) (L : ι → Matrix d d ℂ)
    (X : Matrix d d ℂ) : (gksl H L X).trace = 0 := by
  rw [gksl_apply, trace_add, trace_smul, trace_sub, trace_sum]
  have h1 : (H * X).trace = (X * H).trace := trace_mul_comm H X
  have h2 : ∀ i : ι,
      (L i * X * (L i)ᴴ -
        (2⁻¹ : ℂ) • ((L i)ᴴ * L i * X + X * ((L i)ᴴ * L i))).trace = 0 := by
    intro i
    rw [trace_sub, trace_smul, trace_add]
    have hc : (L i * X * (L i)ᴴ).trace = ((L i)ᴴ * L i * X).trace :=
      trace_mul_cycle (L i) X (L i)ᴴ
    have hc2 : (X * ((L i)ᴴ * L i)).trace = ((L i)ᴴ * L i * X).trace := by
      rw [trace_mul_comm, mul_assoc]
    rw [hc, hc2, smul_eq_mul]
    ring
  rw [Finset.sum_eq_zero fun i _ => h2 i, add_zero, h1, sub_self, smul_zero]

private lemma trace_pair_comm (H X V : Matrix d d ℂ) :
    (((-Complex.I) • (H * X - X * H)) * V).trace =
      (X * (Complex.I • (H * V - V * H))).trace := by
  rw [smul_mul_assoc, mul_smul_comm, trace_smul, trace_smul, sub_mul, mul_sub,
    trace_sub, trace_sub]
  have h1 : (H * X * V).trace = (X * (V * H)).trace := by
    rw [trace_mul_cycle H X V, trace_mul_comm]
  have h2 : (X * H * V).trace = (X * (H * V)).trace := by rw [mul_assoc]
  rw [h1, h2, smul_eq_mul, smul_eq_mul]
  ring

private lemma trace_pair_dissipator (K X V : Matrix d d ℂ) :
    ((K * X * Kᴴ - (2⁻¹ : ℂ) • (Kᴴ * K * X + X * (Kᴴ * K))) * V).trace =
      (X * (Kᴴ * V * K - (2⁻¹ : ℂ) • (Kᴴ * K * V + V * (Kᴴ * K)))).trace := by
  rw [sub_mul, mul_sub, trace_sub, trace_sub, smul_mul_assoc, mul_smul_comm,
    trace_smul, trace_smul, add_mul, mul_add, trace_add, trace_add]
  have hs : (K * X * Kᴴ * V).trace = (X * (Kᴴ * V * K)).trace := by
    rw [mul_assoc (K * X) Kᴴ V, trace_mul_comm, ← mul_assoc (Kᴴ * V) K X,
      trace_mul_comm]
  have ha1 : (Kᴴ * K * X * V).trace = (X * (V * (Kᴴ * K))).trace := by
    rw [mul_assoc (Kᴴ * K) X V, trace_mul_comm, mul_assoc X V (Kᴴ * K)]
  have ha2 : (X * (Kᴴ * K) * V).trace = (X * (Kᴴ * K * V)).trace := by
    rw [mul_assoc]
  rw [hs, ha1, ha2]
  simp only [smul_eq_mul]
  ring

/-- **The Schrödinger↔Heisenberg trace adjunction for the GKSL form**:
`tr((gksl H L X) · V) = tr(X · (gkslDag H L V))` for all `X, V` — the
`hpair` hypothesis of `fence_transport`, discharged with the *computed*
Heisenberg image, for every GKSL mechanism profile. -/
theorem gksl_pairing (H : Matrix d d ℂ) (L : ι → Matrix d d ℂ)
    (X V : Matrix d d ℂ) :
    (gksl H L X * V).trace = (X * gkslDag H L V).trace := by
  rw [gksl_apply, gkslDag_apply, add_mul, mul_add, trace_add, trace_add,
    Finset.sum_mul, Finset.mul_sum, trace_sum, trace_sum]
  congr 1
  · exact trace_pair_comm H X V
  · exact Finset.sum_congr rfl fun i _ => trace_pair_dissipator (L i) X V

end GKSL

end OpenQuantum

end Qtsl

-- Axiom receipts (expected: [propext, Classical.choice, Quot.sound] throughout)
#print axioms Qtsl.OpenQuantum.trace_mul_nonneg
#print axioms Qtsl.OpenQuantum.re_trace_drift_le
#print axioms Qtsl.OpenQuantum.exp_contraction_of_deriv_le
#print axioms Qtsl.OpenQuantum.trace_eq_of_flow
#print axioms Qtsl.OpenQuantum.fence_transport
#print axioms Qtsl.OpenQuantum.gamma_mul_re_trace_le_zeta_of_invariant
#print axioms Qtsl.OpenQuantum.gksl_trace_eq_zero
#print axioms Qtsl.OpenQuantum.gksl_pairing
