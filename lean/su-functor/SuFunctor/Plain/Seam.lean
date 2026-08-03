import SuFunctor.Plain.Penalty
import SuFunctor.Universe.ProbCarrier

/-! # The seam: joints and distributions agree at the finite stratum

Two presentations of the subprobability stock meet here:

* the exact stratum (`SuFunctor.Plain.Penalty`): `Joint X` — finitely
  supported weights `X →₀ ℝ≥0` of total mass at most one, over an
  arbitrary carrier;
* the semantic stratum (`SuFunctor.Universe.Carrier`): `BelState V` —
  pointwise-nonnegative real weight functions of total mass at most
  one, over a finite outcome space.

Over a finite carrier the two are the same object in different
presentations: finite support is automatic, and the nonnegative reals
are exactly the range of the `ℝ≥0` coercion.  This module records the
identification and transports the penalty stock and the satisfaction
judgment across it:

* `jointEquivBel` — the equivalence `Joint V ≃ BelState V` (forward:
  coerce the weights into `ℝ`; backward: truncate — a no-op on the
  nonnegative carrier — and collect the finite support), with the mass
  correspondence (`jointEquivBel_mass`) and preservation of the zero
  state (`jointEquivBel_zero`);
* `jointEquivProb` — the restriction to the mass-one slice,
  `{μ : Joint V // mass one} ≃ ProbState V`, coherent with
  `jointEquivBel` through the two inclusions (`coe_jointEquivProb`,
  `toBel_jointEquivProb`);
* `penEquiv` — the induced order isomorphism of penalty stocks,
  `Pen V ≃o (BelState V → ℝ≥0∞)`, by precomposition with
  `jointEquivBel.symm`, pointwise order on both sides (precomposition
  with the *forward* equivalence does not typecheck; the pin below
  keeps that as an elaboration failure, compare the middle-forgetting
  pin in `SuFunctor.Plain.Battery`);
* `singleton_subset_iff_penEquiv_mem` — the judgment bridge: the
  fibre-order satisfaction judgment (membership of an ideal point,
  `SuFunctor.Plain.Battery: idealPoint_le_iff`) transports along
  `penEquiv` to the semantic penalty stock, where the crescent-class
  machinery consumes it through the `ProbState` restriction
  (`SuFunctor.Universe.VietorisStratum:
  compileNC_mem_crescentClass_iff`).
-/

namespace SuFunctor

namespace Plain

noncomputable section

open scoped NNReal ENNReal

universe u

variable {V : Type u} [Fintype V]

/-! ## The equivalence of subprobability stocks -/

/-- The real-coefficient reading of a joint keeps its mass bound: the
finsupp mass bound of `Joint`, transported through the `ℝ≥0`
coercion. -/
theorem sum_coe_wt_le_one (μ : Joint V) : ∑ v, (μ.wt v : ℝ) ≤ 1 := by
  have h := μ.mass_le_one
  rw [Finsupp.sum_fintype _ _ fun _ => rfl] at h
  have h2 : ((∑ v, μ.wt v : ℝ≥0) : ℝ) ≤ ((1 : ℝ≥0) : ℝ) := NNReal.coe_le_coe.mpr h
  simpa [NNReal.coe_sum] using h2

/-- A joint over a finite carrier, read as a distribution: coerce the
weights into `ℝ`. -/
def toBelState (μ : Joint V) : Universe.BelState V :=
  ⟨fun v => (μ.wt v : ℝ), fun v => (μ.wt v).coe_nonneg, sum_coe_wt_le_one μ⟩

@[simp] theorem coe_toBelState (μ : Joint V) (v : V) :
    ((toBelState μ : Universe.BelState V) : V → ℝ) v = (μ.wt v : ℝ) := rfl

/-- A distribution over a finite carrier, read as a joint: truncate
into `ℝ≥0` (a no-op on the nonnegative carrier) and collect into a
finitely supported function. -/
def ofBelState (x : Universe.BelState V) : Joint V where
  wt := Finsupp.equivFunOnFinite.symm fun v => ((x : V → ℝ) v).toNNReal
  mass_le_one := by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl, ← NNReal.coe_le_coe,
      NNReal.coe_sum, NNReal.coe_one]
    calc ∑ v, ((Finsupp.equivFunOnFinite.symm
            fun v => ((x : V → ℝ) v).toNNReal) v : ℝ)
        = ∑ v, (x : V → ℝ) v := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finsupp.equivFunOnFinite_symm_apply_apply]
          exact Real.coe_toNNReal _ (x.2.1 v)
      _ ≤ 1 := x.2.2

@[simp] theorem wt_ofBelState (x : Universe.BelState V) (v : V) :
    (ofBelState x).wt v = ((x : V → ℝ) v).toNNReal := by
  simp [ofBelState]

/-- **The seam equivalence**: over a finite carrier, finitely supported
subprobability joints and real-valued subprobability distributions are
one stock.  Forward: coerce the weights into `ℝ`; backward: truncate
(a no-op on the nonnegative carrier) and collect the finite support. -/
def jointEquivBel : Joint V ≃ Universe.BelState V where
  toFun := toBelState
  invFun := ofBelState
  left_inv μ := by
    apply Joint.ext
    ext v
    simp
  right_inv x := by
    apply Subtype.ext
    funext v
    show (((ofBelState x).wt v : ℝ≥0) : ℝ) = (x : V → ℝ) v
    rw [wt_ofBelState]
    exact Real.coe_toNNReal _ (x.2.1 v)

@[simp] theorem coe_jointEquivBel (μ : Joint V) (v : V) :
    ((jointEquivBel μ : Universe.BelState V) : V → ℝ) v = (μ.wt v : ℝ) := rfl

@[simp] theorem wt_jointEquivBel_symm (x : Universe.BelState V) (v : V) :
    (jointEquivBel.symm x : Joint V).wt v = ((x : V → ℝ) v).toNNReal :=
  wt_ofBelState x v

/-! ## Mass correspondence -/

/-- **Mass correspondence**: the distribution mass of the image is the
finsupp mass of the source, both read in `ℝ`.  (Mass at most one holds
on both sides by construction.) -/
theorem jointEquivBel_mass (μ : Joint V) :
    ∑ v, ((jointEquivBel μ : Universe.BelState V) : V → ℝ) v
      = μ.wt.sum fun _ v => (v : ℝ) := by
  rw [Finsupp.sum_fintype _ _ fun _ => NNReal.coe_zero]
  simp

variable (V) in
/-- Zero goes to zero: total mass loss is the same point in both
presentations. -/
theorem jointEquivBel_zero :
    jointEquivBel (Joint.zero V) = Universe.BelState.zero V := by
  apply Subtype.ext
  funext v
  simp

/-! ## The mass-one slice -/

/-- **The flat stratum**: joints of total mass exactly one correspond
to probability distributions — the restriction of `jointEquivBel` to
the mass-one slice (compare `SuFunctor.Universe.ProbCarrier`, where
the flat carrier is introduced). -/
def jointEquivProb :
    {μ : Joint V // μ.wt.sum (fun _ v => v) = 1} ≃ Universe.ProbState V where
  toFun μ :=
    ⟨fun v => (μ.1.wt v : ℝ), fun v => (μ.1.wt v).coe_nonneg, by
      have h := μ.2
      rw [Finsupp.sum_fintype _ _ fun _ => rfl] at h
      have h2 : ((∑ v, μ.1.wt v : ℝ≥0) : ℝ) = ((1 : ℝ≥0) : ℝ) := by rw [h]
      simpa [NNReal.coe_sum] using h2⟩
  invFun x :=
    ⟨ofBelState x.toBel, by
      rw [Finsupp.sum_fintype _ _ fun _ => rfl, ← NNReal.coe_inj,
        NNReal.coe_sum, NNReal.coe_one]
      calc ∑ v, ((ofBelState x.toBel).wt v : ℝ)
          = ∑ v, (x : V → ℝ) v := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [wt_ofBelState, Universe.ProbState.toBel_coe]
            exact Real.coe_toNNReal _ (x.nonneg v)
        _ = 1 := x.sum_eq_one⟩
  left_inv μ := by
    apply Subtype.ext
    apply Joint.ext
    ext v
    simp
  right_inv x := by
    apply Subtype.ext
    funext v
    show (((ofBelState x.toBel).wt v : ℝ≥0) : ℝ) = (x : V → ℝ) v
    rw [wt_ofBelState, Universe.ProbState.toBel_coe]
    exact Real.coe_toNNReal _ (x.nonneg v)

/-- The flat-stratum equivalence agrees with the subprobability
equivalence at the level of underlying functions: the square with the
two inclusions (mass-one joints into joints; `ProbState.toBel`)
commutes on coercions. -/
theorem coe_jointEquivProb (μ : {μ : Joint V // μ.wt.sum (fun _ v => v) = 1}) :
    ((jointEquivProb μ : Universe.ProbState V) : V → ℝ)
      = ((jointEquivBel μ.1 : Universe.BelState V) : V → ℝ) :=
  rfl

/-- The inclusion form of `coe_jointEquivProb`: the flat-stratum
equivalence followed by `ProbState.toBel` is the subprobability
equivalence on the underlying joint. -/
theorem toBel_jointEquivProb (μ : {μ : Joint V // μ.wt.sum (fun _ v => v) = 1}) :
    (jointEquivProb μ).toBel = jointEquivBel μ.1 :=
  rfl

/-! ## Penalty transport -/

/-- **Penalty transport**: the seam equivalence induces an order
isomorphism between the exact-stratum penalty stock (`Pen V`,
functions out of joints) and the semantic-stratum penalty stock
(functions out of distributions), by precomposition with
`jointEquivBel.symm`; the order is pointwise on both sides. -/
def penEquiv : Pen V ≃o (Universe.BelState V → ℝ≥0∞) where
  toFun σ := σ ∘ (jointEquivBel (V := V)).symm
  invFun τ := τ ∘ jointEquivBel (V := V)
  left_inv σ := funext fun μ =>
    congrArg σ ((jointEquivBel (V := V)).symm_apply_apply μ)
  right_inv τ := funext fun x =>
    congrArg τ ((jointEquivBel (V := V)).apply_symm_apply x)
  map_rel_iff' {σ σ'} := by
    constructor
    · intro h
      rw [Pi.le_def] at h ⊢
      intro μ
      simpa using h (jointEquivBel μ)
    · intro h
      rw [Pi.le_def] at h ⊢
      intro x
      exact h _

@[simp] theorem penEquiv_apply (σ : Pen V) (x : Universe.BelState V) :
    penEquiv σ x = σ (jointEquivBel.symm x) := rfl

@[simp] theorem penEquiv_symm_apply (τ : Universe.BelState V → ℝ≥0∞)
    (μ : Joint V) : penEquiv.symm τ μ = τ (jointEquivBel μ) := rfl

/-! Transport by precomposition with the *forward* equivalence does not
typecheck — a penalty on joints consumes joints, so the semantic-stratum
penalty can only arise through the inverse.  Kept as an
elaboration-failure pin (compare the middle-forgetting pin in
`SuFunctor.Plain.Battery`). -/
#check_failure fun (σ : Pen V) => σ ∘ ⇑(jointEquivBel (V := V))

/-! ## The judgment bridge -/

/-- **The judgment bridge**: the fibre-order satisfaction judgment on
the exact stratum — membership of an ideal point, in the singleton
form of `SuFunctor.Plain.Battery: idealPoint_le_iff` — transports
along `penEquiv` to the semantic penalty stock: a penalty's singleton
is included in a class iff its transport is a member of the
transported class.  On the semantic side the `ProbState` restriction
of a `BelState` penalty feeds the crescent-class machinery
(`SuFunctor.Universe.VietorisStratum:
compileNC_mem_crescentClass_iff`). -/
theorem singleton_subset_iff_penEquiv_mem (σ : Pen V) (𝒮 : Set (Pen V)) :
    ({σ} : Set (Pen V)) ⊆ 𝒮 ↔ penEquiv σ ∈ penEquiv '' 𝒮 := by
  rw [Set.singleton_subset_iff]
  exact ((penEquiv (V := V)).injective.mem_set_image).symm

end

end Plain

end SuFunctor
