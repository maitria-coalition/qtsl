import SuFunctor.Universe.CredalPoset.Inclusions
import SuFunctor.Universe.CredalPoset.Witnesses
import Mathlib.Data.Fintype.Sum

/-! # Thinning absorption: rate imprecision as stay-channel imprecision

A bounded-intensity jump structure on a finite state space contributes,
at each source state, a *rate* `lam` and a *post-jump law*
`ν : BelState V` — a subprobability whose deficit `1 - ν.mass` is read
as killing (Davis's convention for piecewise-deterministic Markov
processes; cf. Ethier–Kurtz).  Its action on an observable `f` with
source value `c` is the jump-generator functional
`lam * ((∑ v, ν v * f v) - c)`.

At a declared majorant `Lambda ≥ lam`, Poisson **thinning** re-expresses
the pair `(lam, ν)` as a *probability* state on the extended outcome
space `V ⊕ Bool`: jump targets keep the rescaled law, `Sum.inr true` is
an explicit **stay** channel (a phantom jump: the process remains where
it is), and `Sum.inr false` an explicit **kill** channel (the rescaled
deficit).  This module mechanizes the absorption facts for *imprecise*
rates and kernels:

* `thin` / `thinRate` — the chart, division-free core (`thin` takes the
  retention probability `p = lam / Lambda`) and the rate face.  Thinned
  states have **mass one** (`mass_thin`): both channels are explicit, so
  no mass is lost — the chart lands in the full-mass stratum.
* `extGen_thin` / `extGen_thinRate` — **the absorption is lossless**:
  the generator functional recovered from the thinned state (stay reads
  the source value, kill reads `0`) is exactly the original one.
* `extGen_image_thinFamilyRate` — for a *family* (a rate set `R` and a
  kernel body `K`), the set of recovered generator values on the
  absorbed family equals the set of original generator values on
  `R ×ˢ K`; in particular the demonic (sup) and angelic (inf) envelopes
  agree (`sSup_extGen_thinFamilyRate`).  Rate imprecision at a fixed
  majorant *is* stay-channel imprecision.
* `isCozman_scaleSegment_thinFamily` — for closed convex nonempty data
  the absorbed family is a nonempty closed convex set of full-mass
  states, so its radial embedding is a **classical credal set**
  (`IsCozman`), hence a Richardson body, a convex credal body, and a
  credal body, by the landed inclusion chain.  Convexity of the family
  is the re-association arithmetic of convex splits: a mixture of
  thinned states is the thinned mixture at the mixed retention
  probability, with kernel weights `a * p₁ / p` and `b * p₂ / p`.
* `sep_mass_one_scaleSegment` — the family is recovered from its radial
  embedding as the full-mass slice: the credal packaging loses nothing.
  (This is the mass-one instance of the equal-mass slice reconciliation
  used by the demonic adequacy faces.)
* `not_isRadial_of_forall_mass_eq_one` — the honest negative: a
  nonempty family of full-mass states is *never* ray-down closed, so the
  radial embedding step is required, not decorative.
* `not_ptwiseDown_scaleSegment_thinFamily_pair` — a two-outcome witness
  that the radial embedding is not pointwise-down closed: the
  ultracontribution classes (and with them the MWER and finitely
  generated down-closure classes) do not receive absorbed families in
  general.  The stay/kill bookkeeping is rigid; mass cannot leak
  arbitrarily.
* Endpoint probe — the generator functional is linear in the rate, so
  on a rate interval its values are bracketed by the endpoint values
  (`jumpGen_le_max_endpoint`, `min_endpoint_le_jumpGen`): interval
  arithmetic suffices for envelope purposes.  The companion witness
  `probe_coupling_diverges` shows the qualification: a *coupled*
  rate-kernel family with the same marginals can have every generator
  value strictly below a product-family value — envelope agreement
  across joint-body conventions holds for conventions admitting the
  product pairs, and genuinely fails for a bare diagonal.
-/

namespace SuFunctor.Universe.Thinning

open CredalPoset

variable {V : Type*} [Fintype V]

/-! ## The chart -/

/-- The underlying weight function of a thinned state: jump targets
carry the rescaled law, `Sum.inr true` the stay mass, `Sum.inr false`
the rescaled deficit (killing). -/
private def thinFun (p : ℝ) (ν : BelState V) : V ⊕ Bool → ℝ :=
  Sum.elim (fun v => p * (ν : V → ℝ) v)
    (fun b => bif b then 1 - p else p * (1 - ν.mass))

/-- Thinned weights sum to exactly one: the stay channel carries
`1 - p`, the kill channel the rescaled deficit, and the jump targets
the rescaled mass. -/
private theorem sum_thinFun (p : ℝ) (ν : BelState V) :
    ∑ w, thinFun p ν w = 1 := by
  rw [Fintype.sum_sum_type, Fintype.sum_bool]
  show (∑ v, p * (ν : V → ℝ) v)
      + ((1 - p) + p * (1 - ν.mass)) = 1
  rw [← Finset.mul_sum]
  have hm : ∑ v, (ν : V → ℝ) v = ν.mass := rfl
  rw [hm]
  ring

set_option linter.unusedVariables false in
/-- The carrier bound, proven without consulting the exact channel
formulas (an inequality robust to the channel bookkeeping; the exact
identity is `sum_thinFun`).  The bound hypotheses are part of the
robustness contract even where the exact identity would not need
them. -/
private theorem sum_thinFun_le_one (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (ν : BelState V) : ∑ w, thinFun p ν w ≤ 1 := by
  rw [Fintype.sum_sum_type, Fintype.sum_bool]
  simp only [thinFun, Sum.elim_inl, Sum.elim_inr, cond_true, cond_false]
  rw [← Finset.mul_sum]
  have hm : ∑ v, (ν : V → ℝ) v = ν.mass := rfl
  rw [hm]
  nlinarith [ν.mass_nonneg, ν.mass_le_one, h0, h1,
    mul_nonneg h0 ν.mass_nonneg,
    mul_nonneg h0 (sub_nonneg.mpr ν.mass_le_one),
    mul_nonneg (sub_nonneg.mpr h1) ν.mass_nonneg,
    mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr ν.mass_le_one)]

/-- **The thinning chart.**  Thinning a subprobability post-jump law
`ν` at retention probability `p` (for a rate `lam` at majorant
`Lambda`, take `p = lam / Lambda`; see `thinRate`): the extended-space
state with explicit stay and kill channels. -/
def thin (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (ν : BelState V) :
    BelState (V ⊕ Bool) :=
  ⟨thinFun p ν, by
    constructor
    · intro w
      rcases w with v | b
      · exact mul_nonneg h0 (ν.nonneg v)
      · cases b
        · show 0 ≤ thinFun p ν (Sum.inr false)
          simp only [thinFun, Sum.elim_inr, cond_false]
          nlinarith [mul_nonneg h0 (sub_nonneg.mpr ν.mass_le_one)]
        · show 0 ≤ thinFun p ν (Sum.inr true)
          simp only [thinFun, Sum.elim_inr, cond_true]
          nlinarith [sub_nonneg.mpr h1,
            mul_nonneg (sub_nonneg.mpr h1) ν.mass_nonneg]
    · exact sum_thinFun_le_one p h0 h1 ν⟩

@[simp] theorem thin_apply_inl (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (ν : BelState V) (v : V) :
    ((thin p h0 h1 ν : BelState (V ⊕ Bool)) : V ⊕ Bool → ℝ) (Sum.inl v)
      = p * (ν : V → ℝ) v := rfl

@[simp] theorem thin_apply_stay (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (ν : BelState V) :
    ((thin p h0 h1 ν : BelState (V ⊕ Bool)) : V ⊕ Bool → ℝ) (Sum.inr true)
      = 1 - p := rfl

@[simp] theorem thin_apply_kill (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (ν : BelState V) :
    ((thin p h0 h1 ν : BelState (V ⊕ Bool)) : V ⊕ Bool → ℝ) (Sum.inr false)
      = p * (1 - ν.mass) := rfl

/-- **Thinned states have mass one**: with both channels explicit, no
mass is lost — the chart lands in the full-mass stratum of the extended
carrier.  (Compare the closed-law mass fact that feeds the equal-mass
slice reconciliation of the demonic adequacy faces; here the mass is
one *by construction of the chart*.) -/
@[simp] theorem mass_thin (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (ν : BelState V) : (thin p h0 h1 ν).mass = 1 :=
  sum_thinFun p ν

/-- The rate face of the chart: thinning at rate `lam` under majorant
`Lambda`. -/
noncomputable def thinRate (Lambda lam : ℝ) (hb : 0 < Lambda) (h0 : 0 ≤ lam)
    (hle : lam ≤ Lambda) (ν : BelState V) : BelState (V ⊕ Bool) :=
  thin (lam / Lambda) (div_nonneg h0 hb.le) ((div_le_one hb).mpr hle) ν

/-! ## The generator functional and its recovery -/

/-- The jump-generator functional of a rate-and-law pair at an
observable pair `(f, c)` — `f` the observable on jump targets, `c` its
value at the jump's source state.  Sub-stochastic deficit is killing:
the missing mass contributes `0`, so the functional is
`lam * ((∑ v, ν v * f v) - c)`. -/
def jumpGen (lam : ℝ) (ν : BelState V) (f : V → ℝ) (c : ℝ) : ℝ :=
  lam * ((∑ v, (ν : V → ℝ) v * f v) - c)

/-- The extension of an observable pair to the extended outcome space:
jump targets read `f`, the stay channel reads the source value `c`
(a phantom jump changes nothing), the kill channel reads `0` (the dead
state's value). -/
def extObs (f : V → ℝ) (c : ℝ) : V ⊕ Bool → ℝ :=
  Sum.elim f (fun b => bif b then c else 0)

omit [Fintype V] in
@[simp] theorem extObs_inl (f : V → ℝ) (c : ℝ) (v : V) :
    extObs f c (Sum.inl v) = f v := rfl

omit [Fintype V] in
@[simp] theorem extObs_stay (f : V → ℝ) (c : ℝ) :
    extObs f c (Sum.inr true) = c := rfl

omit [Fintype V] in
@[simp] theorem extObs_kill (f : V → ℝ) (c : ℝ) :
    extObs f c (Sum.inr false) = 0 := rfl

/-- The generator functional recovered from an extended-space state at
majorant `Lambda`. -/
def extGen (Lambda : ℝ) (τ : BelState (V ⊕ Bool)) (f : V → ℝ) (c : ℝ) : ℝ :=
  Lambda * ((∑ w, (τ : V ⊕ Bool → ℝ) w * extObs f c w) - c)

/-- **Generator recovery, probability form**: the recovered functional
of a thinned state is the original functional at rate `Lambda * p`.
The stay channel's contribution `(1 - p) * c` cancels against the
`- c`, leaving the thinned rate; the kill channel contributes nothing.
The absorption is lossless. -/
theorem extGen_thin (Lambda p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (ν : BelState V) (f : V → ℝ) (c : ℝ) :
    extGen Lambda (thin p h0 h1 ν) f c = jumpGen (Lambda * p) ν f c := by
  unfold extGen jumpGen
  rw [Fintype.sum_sum_type, Fintype.sum_bool]
  -- the three channels, each read off definitionally: the jump targets
  -- carry the rescaled law against `f`, the stay channel carries
  -- `(1 - p) * c`, and the kill channel is annihilated by the dead
  -- state's value `0`.
  have h_inl : (∑ v, ((thin p h0 h1 ν : BelState (V ⊕ Bool)) : V ⊕ Bool → ℝ)
        (Sum.inl v) * extObs f c (Sum.inl v))
      = ∑ v, (p * (ν : V → ℝ) v) * f v := rfl
  have h_stay : ((thin p h0 h1 ν : BelState (V ⊕ Bool)) : V ⊕ Bool → ℝ)
        (Sum.inr true) * extObs f c (Sum.inr true) = (1 - p) * c := rfl
  have h_kill : ((thin p h0 h1 ν : BelState (V ⊕ Bool)) : V ⊕ Bool → ℝ)
        (Sum.inr false) * extObs f c (Sum.inr false) = 0 := by
    rw [show extObs f c (Sum.inr false) = 0 from rfl]
    exact mul_zero _
  rw [h_inl, h_stay, h_kill]
  have hsum : (∑ v, (p * (ν : V → ℝ) v) * f v)
      = p * ∑ v, (ν : V → ℝ) v * f v := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hsum]
  ring

/-- **Generator recovery, rate form**: thinning at rate `lam` under
majorant `Lambda` and recovering at `Lambda` returns the original
functional at `lam`. -/
theorem extGen_thinRate (Lambda lam : ℝ) (hb : 0 < Lambda) (h0 : 0 ≤ lam)
    (hle : lam ≤ Lambda) (ν : BelState V) (f : V → ℝ) (c : ℝ) :
    extGen Lambda (thinRate Lambda lam hb h0 hle ν) f c
      = jumpGen lam ν f c := by
  rw [thinRate, extGen_thin]
  congr 1
  field_simp

/-! ## Absorbed families -/

/-- The absorbed family of a retention-probability set `M` and a kernel
body `K`: all thinnings of members of `K` at probabilities in `M`. -/
def thinFamily (M : Set ℝ) (K : Set (BelState V)) :
    Set (BelState (V ⊕ Bool)) :=
  {τ | ∃ (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1),
    p ∈ M ∧ ∃ ν ∈ K, τ = thin p h0 h1 ν}

/-- The absorbed family of a rate set `R` and a kernel body `K` at
majorant `Lambda`. -/
def thinFamilyRate (Lambda : ℝ) (R : Set ℝ) (K : Set (BelState V)) :
    Set (BelState (V ⊕ Bool)) :=
  thinFamily ((fun lam => lam / Lambda) '' R) K

theorem thin_mem_thinFamily {M : Set ℝ} {K : Set (BelState V)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hp : p ∈ M) {ν : BelState V} (hν : ν ∈ K) :
    thin p h0 h1 ν ∈ thinFamily M K :=
  ⟨p, h0, h1, hp, ν, hν, rfl⟩

/-- Every member of an absorbed family has mass one: the equal-mass
hypothesis of the slice reconciliation holds at `m = 1` by
construction. -/
theorem mass_eq_one_of_mem_thinFamily {M : Set ℝ} {K : Set (BelState V)}
    {τ : BelState (V ⊕ Bool)} (h : τ ∈ thinFamily M K) : τ.mass = 1 := by
  obtain ⟨p, h0, h1, -, ν, -, rfl⟩ := h
  exact mass_thin p h0 h1 ν

theorem thinFamily_nonempty {M : Set ℝ} {K : Set (BelState V)}
    (hMne : M.Nonempty) (hMsub : M ⊆ Set.Icc 0 1) (hKne : K.Nonempty) :
    (thinFamily M K).Nonempty := by
  obtain ⟨p, hp⟩ := hMne
  obtain ⟨ν, hν⟩ := hKne
  exact ⟨thin p (hMsub hp).1 (hMsub hp).2 ν,
    thin_mem_thinFamily (hMsub hp).1 (hMsub hp).2 hp hν⟩

/-! ## Envelope preservation -/

/-- **Envelope preservation, set form**: the recovered generator values
on the absorbed family are exactly the original generator values on the
rate-kernel product.  Both the demonic (sup) and the angelic (inf)
envelope agree, since the value sets are equal. -/
theorem extGen_image_thinFamilyRate {Lambda : ℝ} (hb : 0 < Lambda)
    {R : Set ℝ} (hR : R ⊆ Set.Icc 0 Lambda) (K : Set (BelState V))
    (f : V → ℝ) (c : ℝ) :
    (fun τ => extGen Lambda τ f c) '' thinFamilyRate Lambda R K
      = (fun q : ℝ × BelState V => jumpGen q.1 q.2 f c) '' (R ×ˢ K) := by
  ext x
  constructor
  · rintro ⟨τ, ⟨p, h0, h1, ⟨lam, hlam, rfl⟩, ν, hν, rfl⟩, rfl⟩
    refine ⟨(lam, ν), ⟨hlam, hν⟩, ?_⟩
    exact (extGen_thinRate Lambda lam hb (hR hlam).1 (hR hlam).2 ν f c).symm
  · rintro ⟨⟨lam, ν⟩, ⟨hlam, hν⟩, rfl⟩
    refine ⟨thinRate Lambda lam hb (hR hlam).1 (hR hlam).2 ν,
      ⟨lam / Lambda, div_nonneg (hR hlam).1 hb.le,
        (div_le_one hb).mpr (hR hlam).2, ⟨lam, hlam, rfl⟩, ν, hν, rfl⟩, ?_⟩
    exact extGen_thinRate Lambda lam hb (hR hlam).1 (hR hlam).2 ν f c

/-- **Demonic-envelope preservation**: the supremum of recovered
generator values over the absorbed family equals the supremum of
original generator values over the rate-kernel product. -/
theorem sSup_extGen_thinFamilyRate {Lambda : ℝ} (hb : 0 < Lambda)
    {R : Set ℝ} (hR : R ⊆ Set.Icc 0 Lambda) (K : Set (BelState V))
    (f : V → ℝ) (c : ℝ) :
    sSup ((fun τ => extGen Lambda τ f c) '' thinFamilyRate Lambda R K)
      = sSup ((fun q : ℝ × BelState V => jumpGen q.1 q.2 f c) '' (R ×ˢ K)) := by
  rw [extGen_image_thinFamilyRate hb hR K f c]

/-! ## Topological and convex structure of the absorbed family -/

/-- The chart as a bare map on ambient spaces (no membership proofs):
the continuity carrier for the compactness argument. -/
private def thinAux : ℝ × (V → ℝ) → (V ⊕ Bool) → ℝ := fun q =>
  Sum.elim (fun v => q.1 * q.2 v)
    (fun b => bif b then 1 - q.1 else q.1 * (1 - ∑ v, q.2 v))

private theorem continuous_thinAux :
    Continuous (thinAux (V := V)) := by
  refine continuous_pi fun w => ?_
  rcases w with v | b
  · show Continuous fun q : ℝ × (V → ℝ) => q.1 * q.2 v
    exact continuous_fst.mul ((continuous_apply v).comp continuous_snd)
  · cases b
    · show Continuous fun q : ℝ × (V → ℝ) => q.1 * (1 - ∑ v, q.2 v)
      exact continuous_fst.mul (continuous_const.sub
        (continuous_finsetSum _ fun v _ =>
          (continuous_apply v).comp continuous_snd))
    · show Continuous fun q : ℝ × (V → ℝ) => 1 - q.1
      exact continuous_const.sub continuous_fst

/-- **The absorbed family is compact** for closed data: it is the
continuous image of `M ×ˢ K` under the chart. -/
theorem isCompact_thinFamily {M : Set ℝ} {K : Set (BelState V)}
    (hMcl : IsClosed M) (hMsub : M ⊆ Set.Icc 0 1) (hKcl : IsClosed K) :
    IsCompact (thinFamily M K) := by
  rw [Topology.IsInducing.subtypeVal.isCompact_iff]
  have hMcp : IsCompact M :=
    IsCompact.of_isClosed_subset isCompact_Icc hMcl hMsub
  have hKval : IsCompact (Subtype.val '' K) :=
    hKcl.isCompact.image continuous_subtype_val
  have him : Subtype.val '' thinFamily M K
      = thinAux '' (M ×ˢ (Subtype.val '' K)) := by
    ext y
    constructor
    · rintro ⟨τ, ⟨p, h0, h1, hpM, ν, hν, rfl⟩, rfl⟩
      exact ⟨(p, (ν : V → ℝ)), ⟨hpM, ν, hν, rfl⟩, rfl⟩
    · rintro ⟨⟨p, z⟩, ⟨hpM, ν, hν, rfl⟩, rfl⟩
      exact ⟨thin p (hMsub hpM).1 (hMsub hpM).2 ν,
        thin_mem_thinFamily (hMsub hpM).1 (hMsub hpM).2 hpM hν, rfl⟩
  rw [him]
  exact (hMcp.prod hKval).image continuous_thinAux

theorem isClosed_thinFamily {M : Set ℝ} {K : Set (BelState V)}
    (hMcl : IsClosed M) (hMsub : M ⊆ Set.Icc 0 1) (hKcl : IsClosed K) :
    IsClosed (thinFamily M K) :=
  (isCompact_thinFamily hMcl hMsub hKcl).isClosed

/-- **The absorbed family is a convex body** for convex data.  The
crux computation: a mixture of thinned states is the thinned mixture,
at retention probability `p = a * p₁ + b * p₂` with kernel weights
`a * p₁ / p` and `b * p₂ / p` — the re-association arithmetic of convex
splits.  The corner `p = 0` degenerates to pure stay. -/
theorem convexBody_thinFamily {M : Set ℝ} {K : Set (BelState V)}
    (hMcv : Convex ℝ M) (hKcv : ConvexBody K) :
    ConvexBody (thinFamily M K) := by
  rintro y₁ ⟨τ₁, ⟨p₁, h01, h11, hp₁M, ν₁, hν₁, rfl⟩, rfl⟩
    y₂ ⟨τ₂, ⟨p₂, h02, h12, hp₂M, ν₂, hν₂, rfl⟩, rfl⟩ a b ha hb hab
  have hpM : a * p₁ + b * p₂ ∈ M := by
    have := hMcv hp₁M hp₂M ha hb hab
    simpa [smul_eq_mul] using this
  have h0p : 0 ≤ a * p₁ + b * p₂ :=
    add_nonneg (mul_nonneg ha h01) (mul_nonneg hb h02)
  have h1p : a * p₁ + b * p₂ ≤ 1 := by nlinarith
  by_cases hp0 : a * p₁ + b * p₂ = 0
  · -- both scaled probabilities vanish: the mixture is pure stay
    have hap : a * p₁ = 0 := by nlinarith [mul_nonneg ha h01, mul_nonneg hb h02]
    have hbp : b * p₂ = 0 := by nlinarith [mul_nonneg ha h01, mul_nonneg hb h02]
    refine ⟨thin 0 le_rfl zero_le_one ν₁,
      thin_mem_thinFamily le_rfl zero_le_one (by rwa [hp0] at hpM) hν₁, ?_⟩
    funext w
    rcases w with v | b'
    · show (0 : ℝ) * (ν₁ : V → ℝ) v
        = a * (p₁ * (ν₁ : V → ℝ) v) + b * (p₂ * (ν₂ : V → ℝ) v)
      have h1 : a * (p₁ * (ν₁ : V → ℝ) v) = 0 := by
        rw [← mul_assoc, hap, zero_mul]
      have h2 : b * (p₂ * (ν₂ : V → ℝ) v) = 0 := by
        rw [← mul_assoc, hbp, zero_mul]
      rw [h1, h2, zero_mul, add_zero]
    · cases b'
      · show (0 : ℝ) * (1 - ν₁.mass)
          = a * (p₁ * (1 - ν₁.mass)) + b * (p₂ * (1 - ν₂.mass))
        have h1 : a * (p₁ * (1 - ν₁.mass)) = 0 := by
          rw [← mul_assoc, hap, zero_mul]
        have h2 : b * (p₂ * (1 - ν₂.mass)) = 0 := by
          rw [← mul_assoc, hbp, zero_mul]
        rw [h1, h2, zero_mul, add_zero]
      · show (1 : ℝ) - 0 = a * (1 - p₁) + b * (1 - p₂)
        have : a * p₁ + b * p₂ = 0 := hp0
        nlinarith
  · -- the generic corner: reweighted mixture inside the kernel body
    have hppos : 0 < a * p₁ + b * p₂ := lt_of_le_of_ne h0p (Ne.symm hp0)
    set p := a * p₁ + b * p₂ with hpdef
    have hpne : p ≠ 0 := hppos.ne'
    have hw₁ : 0 ≤ a * p₁ / p := div_nonneg (mul_nonneg ha h01) hppos.le
    have hw₂ : 0 ≤ b * p₂ / p := div_nonneg (mul_nonneg hb h02) hppos.le
    have hwsum : a * p₁ / p + b * p₂ / p = 1 := by
      rw [← add_div, ← hpdef, div_self hpne]
    have hmix : (a * p₁ / p) • (ν₁ : V → ℝ) + (b * p₂ / p) • (ν₂ : V → ℝ)
        ∈ carrierImage K :=
      hKcv (mem_carrierImage hν₁) (mem_carrierImage hν₂) hw₁ hw₂ hwsum
    obtain ⟨ν, hνK, hνcoe⟩ := hmix
    have hνv : ∀ v, (ν : V → ℝ) v
        = (a * p₁ / p) * (ν₁ : V → ℝ) v + (b * p₂ / p) * (ν₂ : V → ℝ) v := by
      intro v
      have := congrFun hνcoe v
      simpa [smul_eq_mul] using this
    have hνmass : ν.mass = (a * p₁ / p) * ν₁.mass + (b * p₂ / p) * ν₂.mass := by
      unfold BelState.mass
      rw [show (∑ v, (ν : V → ℝ) v)
          = ∑ v, ((a * p₁ / p) * (ν₁ : V → ℝ) v
            + (b * p₂ / p) * (ν₂ : V → ℝ) v) from
        Finset.sum_congr rfl fun v _ => hνv v]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    refine ⟨thin p h0p h1p ν, thin_mem_thinFamily h0p h1p hpM hνK, ?_⟩
    funext w
    rcases w with v | b'
    · show p * (ν : V → ℝ) v
        = a * (p₁ * (ν₁ : V → ℝ) v) + b * (p₂ * (ν₂ : V → ℝ) v)
      rw [hνv v]
      field_simp
    · cases b'
      · show p * (1 - ν.mass)
          = a * (p₁ * (1 - ν₁.mass)) + b * (p₂ * (1 - ν₂.mass))
        rw [hνmass]
        have hexp : p * (1 - ((a * p₁ / p) * ν₁.mass + (b * p₂ / p) * ν₂.mass))
            = p - (a * p₁) * ν₁.mass - (b * p₂) * ν₂.mass := by
          field_simp
          ring
        rw [hexp, hpdef]
        ring
      · show (1 : ℝ) - p = a * (1 - p₁) + b * (1 - p₂)
        rw [hpdef]
        nlinarith

/-! ## The credal landing: the classical corner of the poset -/

/-- **The absorption lands in the classical corner**: for closed convex
nonempty data, the radial embedding of the absorbed family is a Cozman
classical credal set — a nonempty closed convex set of full-mass states,
radially embedded.  The landed inclusion chain then yields Richardson,
convex-credal-body, and credal-body membership. -/
theorem isCozman_scaleSegment_thinFamily {M : Set ℝ} {K : Set (BelState V)}
    (hMne : M.Nonempty) (hMcl : IsClosed M) (hMcv : Convex ℝ M)
    (hMsub : M ⊆ Set.Icc 0 1)
    (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : ConvexBody K) :
    IsCozman (scaleSegment (thinFamily M K)) :=
  ⟨thinFamily M K, thinFamily_nonempty hMne hMsub hKne,
    isClosed_thinFamily hMcl hMsub hKcl, convexBody_thinFamily hMcv hKcv,
    fun _ hτ => mass_eq_one_of_mem_thinFamily hτ, rfl⟩

theorem isRichardsonBody_scaleSegment_thinFamily {M : Set ℝ}
    {K : Set (BelState V)}
    (hMne : M.Nonempty) (hMcl : IsClosed M) (hMcv : Convex ℝ M)
    (hMsub : M ⊆ Set.Icc 0 1)
    (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : ConvexBody K) :
    IsRichardsonBody (scaleSegment (thinFamily M K)) :=
  (isCozman_scaleSegment_thinFamily hMne hMcl hMcv hMsub hKne hKcl
    hKcv).isRichardsonBody

theorem isConvexCredalBody_scaleSegment_thinFamily {M : Set ℝ}
    {K : Set (BelState V)}
    (hMne : M.Nonempty) (hMcl : IsClosed M) (hMcv : Convex ℝ M)
    (hMsub : M ⊆ Set.Icc 0 1)
    (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : ConvexBody K) :
    IsConvexCredalBody (scaleSegment (thinFamily M K)) :=
  haveI : Nonempty (V ⊕ Bool) := ⟨Sum.inr true⟩
  (isRichardsonBody_scaleSegment_thinFamily hMne hMcl hMcv hMsub hKne hKcl
    hKcv).isConvexCredalBody

theorem isCredalBody_scaleSegment_thinFamily {M : Set ℝ}
    {K : Set (BelState V)}
    (hMne : M.Nonempty) (hMcl : IsClosed M) (hMcv : Convex ℝ M)
    (hMsub : M ⊆ Set.Icc 0 1)
    (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : ConvexBody K) :
    IsCredalBody (scaleSegment (thinFamily M K)) :=
  (isConvexCredalBody_scaleSegment_thinFamily hMne hMcl hMcv hMsub hKne hKcl
    hKcv).isCredalBody

/-! ### The rate face of the landing -/

section RateFace

variable {Lambda : ℝ} {R : Set ℝ}

private theorem rateSet_nonempty (hRne : R.Nonempty) :
    ((fun lam => lam / Lambda) '' R).Nonempty :=
  hRne.image _

private theorem rateSet_subset (hb : 0 < Lambda) (hR : R ⊆ Set.Icc 0 Lambda) :
    (fun lam => lam / Lambda) '' R ⊆ Set.Icc 0 1 := by
  rintro - ⟨lam, hlam, rfl⟩
  exact ⟨div_nonneg (hR hlam).1 hb.le, (div_le_one hb).mpr (hR hlam).2⟩

private theorem rateSet_isClosed (hRcl : IsClosed R)
    (hR : R ⊆ Set.Icc 0 Lambda) :
    IsClosed ((fun lam => lam / Lambda) '' R) := by
  have hRcp : IsCompact R :=
    IsCompact.of_isClosed_subset isCompact_Icc hRcl hR
  exact (hRcp.image (continuous_id.div_const Lambda)).isClosed

private theorem rateSet_convex (hRcv : Convex ℝ R) :
    Convex ℝ ((fun lam => lam / Lambda) '' R) := by
  rintro - ⟨l₁, hl₁, rfl⟩ - ⟨l₂, hl₂, rfl⟩ a b ha hb' hab
  refine ⟨a * l₁ + b * l₂, ?_, ?_⟩
  · have := hRcv hl₁ hl₂ ha hb' hab
    simpa [smul_eq_mul] using this
  · simp [smul_eq_mul, add_div, mul_div_assoc]

/-- The rate-face landing: for a nonempty closed convex rate set
`R ⊆ [0, Lambda]` and a nonempty closed convex kernel body, the radial
embedding of the rate-absorbed family is a Cozman classical credal
set. -/
theorem isCozman_scaleSegment_thinFamilyRate (hb : 0 < Lambda)
    (hRne : R.Nonempty) (hRcl : IsClosed R) (hRcv : Convex ℝ R)
    (hR : R ⊆ Set.Icc 0 Lambda)
    {K : Set (BelState V)}
    (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : ConvexBody K) :
    IsCozman (scaleSegment (thinFamilyRate Lambda R K)) :=
  isCozman_scaleSegment_thinFamily (rateSet_nonempty hRne)
    (rateSet_isClosed hRcl hR) (rateSet_convex hRcv)
    (rateSet_subset hb hR) hKne hKcl hKcv

theorem isCredalBody_scaleSegment_thinFamilyRate (hb : 0 < Lambda)
    (hRne : R.Nonempty) (hRcl : IsClosed R) (hRcv : Convex ℝ R)
    (hR : R ⊆ Set.Icc 0 Lambda)
    {K : Set (BelState V)}
    (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : ConvexBody K) :
    IsCredalBody (scaleSegment (thinFamilyRate Lambda R K)) :=
  isCredalBody_scaleSegment_thinFamily (rateSet_nonempty hRne)
    (rateSet_isClosed hRcl hR) (rateSet_convex hRcv)
    (rateSet_subset hb hR) hKne hKcl hKcv

end RateFace

/-! ## Slice recovery: the packaging loses nothing -/

/-- For a family of full-mass states, the full-mass slice of its radial
embedding is the family itself — the mass-one instance of the
equal-mass slice reconciliation.  The absorbed family is recoverable
from its credal packaging. -/
theorem sep_mass_one_scaleSegment {W : Type*} [Fintype W]
    {S : Set (BelState W)} (hS : ∀ x ∈ S, x.mass = 1) :
    {x ∈ scaleSegment S | x.mass = 1} = S := by
  ext z
  constructor
  · rintro ⟨⟨x, hx, t, ht0, ht1, rfl⟩, hz1⟩
    rw [mass_scale, hS x hx, mul_one] at hz1
    subst hz1
    have hxeq : BelState.scale 1 ht0 ht1 x = x :=
      Subtype.ext (by rw [BelState.coe_scale, one_smul])
    rwa [hxeq]
  · intro hz
    exact ⟨subset_scaleSegment S hz, hS z hz⟩

/-- Slice recovery for absorbed families. -/
theorem sep_mass_one_scaleSegment_thinFamily (M : Set ℝ)
    (K : Set (BelState V)) :
    {τ ∈ scaleSegment (thinFamily M K) | τ.mass = 1} = thinFamily M K :=
  sep_mass_one_scaleSegment fun _ hτ => mass_eq_one_of_mem_thinFamily hτ

/-! ## Honest negatives -/

/-- A nonempty family of full-mass states is never ray-down closed:
scaling any member by `½` drops its mass to `½`.  The raw absorbed
family is therefore never itself a credal body — the radial embedding
step in the landing theorems is required, not decorative. -/
theorem not_isRadial_of_forall_mass_eq_one {W : Type*} [Fintype W]
    {S : Set (BelState W)} (hne : S.Nonempty) (hS : ∀ x ∈ S, x.mass = 1) :
    ¬ IsRadial S := by
  obtain ⟨x, hx⟩ := hne
  intro hrad
  have hhalf := hrad x hx (1 / 2) (by norm_num) (by norm_num)
  have hmass := hS _ hhalf
  rw [mass_scale, hS x hx, mul_one] at hmass
  norm_num at hmass

/-- The raw absorbed family is not radial (whenever nonempty). -/
theorem not_isRadial_thinFamily {M : Set ℝ} {K : Set (BelState V)}
    (hMne : M.Nonempty) (hMsub : M ⊆ Set.Icc 0 1) (hKne : K.Nonempty) :
    ¬ IsRadial (thinFamily M K) :=
  not_isRadial_of_forall_mass_eq_one
    (thinFamily_nonempty hMne hMsub hKne)
    (fun _ hτ => mass_eq_one_of_mem_thinFamily hτ)

section PtwiseWitness

/-- The uniform post-jump law on a two-outcome space. -/
private noncomputable def halfHalf : BelState Bool :=
  ⟨fun _ => 1 / 2, by
    constructor
    · intro v; norm_num
    · rw [Fintype.sum_bool]; norm_num⟩

private theorem mass_halfHalf : (halfHalf).mass = 1 := by
  show ∑ b, ((halfHalf : BelState Bool) : Bool → ℝ) b = 1
  rw [Fintype.sum_bool]
  show (1 : ℝ) / 2 + 1 / 2 = 1
  norm_num

/-- A state pointwise below a thinned uniform law that is not itself in
the radial embedding of the absorbed family: half the mass on one jump
target, nothing anywhere else. -/
private noncomputable def belowState : BelState (Bool ⊕ Bool) :=
  ⟨fun w => match w with
    | Sum.inl true => 1 / 2
    | _ => 0, by
    constructor
    · intro w
      rcases w with v | b
      · rcases v with _ | _
        · norm_num
        · norm_num
      · rcases b with _ | _
        · norm_num
        · norm_num
    · rw [Fintype.sum_sum_type, Fintype.sum_bool, Fintype.sum_bool]
      norm_num⟩

/-- **Pointwise-down closure fails for the credal packaging**: over the
two-outcome space, the radial embedding of the absorbed family of the
single retention probability `1` and the single uniform kernel does not
contain a state pointwise below one of its members.  The stay/kill
bookkeeping is rigid — mass cannot leak from one jump target alone —
so the ultracontribution classes do not receive absorbed families in
general. -/
theorem not_ptwiseDown_scaleSegment_thinFamily_pair :
    ¬ PtwiseDown
      (scaleSegment (thinFamily ({1} : Set ℝ) ({halfHalf} : Set (BelState Bool)))) := by
  intro h
  have hτmem : thin 1 zero_le_one le_rfl halfHalf
      ∈ thinFamily ({1} : Set ℝ) ({halfHalf} : Set (BelState Bool)) :=
    thin_mem_thinFamily zero_le_one le_rfl (Set.mem_singleton_iff.mpr rfl)
      (Set.mem_singleton_iff.mpr rfl)
  have hle : (belowState : Bool ⊕ Bool → ℝ)
      ≤ ((thin 1 zero_le_one le_rfl halfHalf : BelState (Bool ⊕ Bool))
        : Bool ⊕ Bool → ℝ) := by
    intro w
    rcases w with v | b
    · rcases v with _ | _
      · show (0 : ℝ) ≤ 1 * (1 / 2)
        norm_num
      · show (1 : ℝ) / 2 ≤ 1 * (1 / 2)
        norm_num
    · rcases b with _ | _
      · show (0 : ℝ) ≤ 1 * (1 - halfHalf.mass)
        rw [mass_halfHalf]
        norm_num
      · show (0 : ℝ) ≤ 1 - 1
        norm_num
  have hmem := h _ (subset_scaleSegment _ hτmem) belowState hle
  obtain ⟨y, ⟨p, h0, h1, hp1, ν, hν, rfl⟩, t, ht0, ht1, heq⟩ := hmem
  have hp : p = 1 := Set.eq_of_mem_singleton hp1
  have hνh : ν = halfHalf := Set.eq_of_mem_singleton hν
  subst hp
  subst hνh
  have h₁ : (1 : ℝ) / 2 = t * (1 * (1 / 2)) :=
    congrFun (congrArg Subtype.val heq) (Sum.inl true)
  have h₂ : (0 : ℝ) = t * (1 * (1 / 2)) :=
    congrFun (congrArg Subtype.val heq) (Sum.inl false)
  rw [← h₂] at h₁
  norm_num at h₁

/-- With pointwise-down closure refuted, the packaging is no
ultracontribution: the Kosoy–Appel class (and with it the
Halpern–Leung and Mio–Vignudelli–Sarkis classes, which the landed
inclusions place inside it) does not receive absorbed families in
general. -/
theorem not_isUltra_scaleSegment_thinFamily_pair :
    ¬ IsUltra
      (scaleSegment (thinFamily ({1} : Set ℝ) ({halfHalf} : Set (BelState Bool)))) :=
  fun h => not_ptwiseDown_scaleSegment_thinFamily_pair h.2.2.2

end PtwiseWitness

/-! ## The endpoint probe: joint-body conventions for composite
imprecision -/

/-- The generator functional is linear in the rate, so on a rate
interval its values are dominated by an endpoint value: interval
arithmetic suffices for the demonic envelope of a rate-imprecise
family. -/
theorem jumpGen_le_max_endpoint {a b lam : ℝ} (h : lam ∈ Set.Icc a b)
    (ν : BelState V) (f : V → ℝ) (c : ℝ) :
    jumpGen lam ν f c ≤ max (jumpGen a ν f c) (jumpGen b ν f c) := by
  unfold jumpGen
  rcases le_total 0 ((∑ v, (ν : V → ℝ) v * f v) - c) with hg | hg
  · exact le_max_of_le_right (mul_le_mul_of_nonneg_right h.2 hg)
  · exact le_max_of_le_left (mul_le_mul_of_nonpos_right h.1 hg)

/-- The angelic twin: interval values dominate an endpoint value from
below. -/
theorem min_endpoint_le_jumpGen {a b lam : ℝ} (h : lam ∈ Set.Icc a b)
    (ν : BelState V) (f : V → ℝ) (c : ℝ) :
    min (jumpGen a ν f c) (jumpGen b ν f c) ≤ jumpGen lam ν f c := by
  unfold jumpGen
  rcases le_total 0 ((∑ v, (ν : V → ℝ) v * f v) - c) with hg | hg
  · exact min_le_of_left_le (mul_le_mul_of_nonneg_right h.1 hg)
  · exact min_le_of_right_le (mul_le_mul_of_nonpos_right h.2 hg)

section CouplingWitness

/-- The indicator observable on the two-outcome space. -/
private def indTrue : Bool → ℝ := fun v => bif v then 1 else 0

/-- **The divergence witness**: a coupled rate-kernel family with the
same marginals as the product family (rates `{1, 2}`, kernels the two
point masses) whose generator values all lie strictly below a product
value.  The generator functional is bilinear, and its envelope over a
product factorizes through the rate endpoints — but a joint body that
pairs the low rate with the high-value kernel and the high rate with
the low-value kernel attains neither: envelope agreement across
joint-body conventions holds for conventions containing the product
pairs, and genuinely fails for a bare diagonal. -/
theorem probe_coupling_diverges :
    ∃ x ∈ (fun q : ℝ × BelState Bool => jumpGen q.1 q.2 indTrue 0) ''
        (({1, 2} : Set ℝ) ×ˢ
          ({BelState.dirac true, BelState.dirac false} : Set (BelState Bool))),
      ∀ y ∈ (fun q : ℝ × BelState Bool => jumpGen q.1 q.2 indTrue 0) ''
        ({((1 : ℝ), BelState.dirac true), ((2 : ℝ), BelState.dirac false)}
          : Set (ℝ × BelState Bool)),
      y < x := by
  have hval : ∀ (lam : ℝ) (v : Bool),
      jumpGen lam (BelState.dirac v) indTrue 0 = lam * indTrue v := by
    intro lam v
    show lam * ((∑ b, ((BelState.dirac v : BelState Bool) : Bool → ℝ) b
        * indTrue b) - 0) = lam * indTrue v
    rw [Fintype.sum_bool]
    rcases v with _ | _
    · rw [BelState.dirac_apply_of_ne (v := false) (w := true) (by decide),
        BelState.dirac_apply_same]
      show lam * ((0 * indTrue true + 1 * indTrue false) - 0)
          = lam * indTrue false
      ring
    · rw [BelState.dirac_apply_same,
        BelState.dirac_apply_of_ne (v := true) (w := false) (by decide)]
      show lam * ((1 * indTrue true + 0 * indTrue false) - 0)
          = lam * indTrue true
      ring
  refine ⟨jumpGen 2 (BelState.dirac true) indTrue 0,
    ⟨(2, BelState.dirac true),
      ⟨Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl)),
        Set.mem_insert _ _⟩, rfl⟩, ?_⟩
  rintro y ⟨q, hmem, rfl⟩
  rcases hmem with rfl | hq
  · show jumpGen 1 (BelState.dirac true) indTrue 0
      < jumpGen 2 (BelState.dirac true) indTrue 0
    rw [hval, hval]
    show (1 : ℝ) * 1 < 2 * 1
    norm_num
  · rw [Set.mem_singleton_iff] at hq
    subst hq
    show jumpGen 2 (BelState.dirac false) indTrue 0
      < jumpGen 2 (BelState.dirac true) indTrue 0
    rw [hval, hval]
    show (2 : ℝ) * 0 < 2 * 1
    norm_num

/-- The coupled family has the same rate marginal as the product. -/
theorem probe_coupling_fst :
    Prod.fst '' ({((1 : ℝ), BelState.dirac true),
        ((2 : ℝ), BelState.dirac false)} : Set (ℝ × BelState Bool))
      = ({1, 2} : Set ℝ) := by
  rw [Set.image_insert_eq, Set.image_singleton]

/-- The coupled family has the same kernel marginal as the product. -/
theorem probe_coupling_snd :
    Prod.snd '' ({((1 : ℝ), BelState.dirac true),
        ((2 : ℝ), BelState.dirac false)} : Set (ℝ × BelState Bool))
      = ({BelState.dirac true, BelState.dirac false} : Set (BelState Bool)) := by
  rw [Set.image_insert_eq, Set.image_singleton]

end CouplingWitness

end SuFunctor.Universe.Thinning
