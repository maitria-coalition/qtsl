import QtslAux.BagLift
import Mathlib.Algebra.MvPolynomial.Funext

/-! # The nesting coherence fixture

A two-level nested system, machine-checked: an SDCPN whose token
colors are SDCPNs — ground OU color, inner bag with a death transition
(rate ρ), outer bag of inner bags with a death transition (rate γ) —
built by applying `ColorModel.bag` TWICE (`B₂ := B₁.bag …`: the output
re-entered as input, which is delta 3's closure exercised for real,
and nesting-as-function-composition enacted).

Checks:
* `twoLevel_V` — the boxed identity
  $\mathcal{A}_{S_2} S_s = -(a+\rho+\gamma) S_s$ at the fixture cell,
  mode $(K=2; n_1=1, n_2=2)$, by direct evaluation of the flat
  generator (which at a concrete mode IS the explicit-token/flattened
  generator — the cell check and the boxed identity in one
  statement).
* `twoLevel_W` — the four-block boxed identity for $S_s^2$, including
  BOTH dictionary-growth species: $S_{s_2}$ (inner mint, pooled
  through both levels) and $S_{s^2}$ (outer mint).
* `mu_coherence_cell` — the γ = 0 μ-coherence law at the same mode: on
  a μ*-pulled-back certificate, the twice-lifted flat reading is the
  once-lifted flat reading at the flattened stratum, transported along
  `Equiv.sigmaAssoc` (the polynomial-stratum shadow of `BagMonad`'s
  `bagMu`). SCOPE: the μ-law is the
  edge-free/group-blind fragment only — an outer γ > 0 death reads
  exactly the structure μ forgets (the general compile-compatibility
  half is `mu_compat_pool` in `BagLift.lean`); μ-flattening ≠
  GSHS-flattening (the latter is a separate, staged development).

**Parameters** are concrete distinct primes a = 2, ρ = 3, γ = 5,
σ = 7 (concrete over symbolic, deliberately: frozen-parameter
coordinates would be pooled and count-multiplied in a tower, so the
symbolic route conflicts with the pool discipline; distinct
primes make coefficient-collision cancellations implausible).

Note how the SECOND lift's closure witnesses at the pulled-back
dictionary (`muRep₁ := dRep₁`, literally) are inherited from the first
lift's linearity — the tower feeds itself, as the inductive-stage
story predicts. -/

open MvPolynomial

namespace Qtsl

namespace BagLift

namespace Fixture

open SdeGeneratorPoly

/-- Evaluation pushes through substitution (the `eval` face of
`eval₂Hom_bind₁`; mathlib carries only the `aeval`/`eval₂Hom`
versions). -/
theorem eval_bind₁ {σ τ : Type*} (f : τ → ℚ) (g : σ → MvPolynomial τ ℚ)
    (p : MvPolynomial σ ℚ) :
    eval f (bind₁ g p) = eval (fun i => eval f (g i)) p :=
  eval₂Hom_bind₁ (RingHom.id ℚ) f g p

/-! ## Level 0: the atomic OU color (drift −2x, diffusion 7) -/

noncomputable def P₀ : PolyProfile 1 1 where
  f := fun _ => C (-2) * X 0
  σp := fun _ _ => C 7
  kill := 0
  legs := []

@[reducible] noncomputable def CM₀ : ColorModel PUnit.{2} (Fin 1) :=
  ColorModel.atomic P₀

/-! ## Level 1: `Bag(OU)` with a death transition at rate ρ = 3

Inner dictionary {1, x}: count and colour-sum. -/

noncomputable def Φ₁ : Fin 2 → MvPolynomial (Fin 1) ℚ
  | 0 => 1
  | 1 => X 0

/-- The inner death edge: arity 1, no births, constant rate ρ = 3. -/
@[reducible] noncomputable def death₁ : CM₀.BagEdge (Fin 2) Φ₁ where
  a := 1
  b := 0
  rate := C 3
  MixIx := PUnit
  w := fun _ => 1
  bStrat := fun _ p => p.elim0
  bg := fun _ p => p.elim0
  bKer := fun _ _ _ p => p.elim0
  hbKer := fun _ _ _ p => p.elim0

noncomputable def dRep₁ : Fin 2 → Fin 2 →₀ ℚ
  | 0 => 0
  | 1 => Finsupp.single 1 (-2)

noncomputable def GRep₁ : Fin 2 → Fin 2 → Fin 2 →₀ ℚ
  | 1, 1 => Finsupp.single 0 49
  | _, _ => 0

theorem hdRep₁ (j' : Fin 2) :
    CM₀.contRead (Φ₁ j') = (dRep₁ j').sum fun k a => C a * Φ₁ k := by
  fin_cases j'
  · show CM₀.contRead (Φ₁ 0) = (dRep₁ 0).sum fun k a => C a * Φ₁ k
    rw [show Φ₁ 0 = 1 from rfl, show dRep₁ 0 = 0 from rfl,
      Finsupp.sum_zero_index]
    exact contOp_one _ _
  · show CM₀.contRead (Φ₁ 1) = (dRep₁ 1).sum fun k a => C a * Φ₁ k
    rw [show Φ₁ 1 = X 0 from rfl, show dRep₁ 1 = Finsupp.single 1 (-2 : ℚ) from rfl,
      ColorModel.contRead_X, Finsupp.sum_single_index (by simp)]
    rfl

theorem hGRep₁ (j' l' : Fin 2) :
    CM₀.gramRead (Φ₁ j') (Φ₁ l') = (GRep₁ j' l').sum fun k a => C a * Φ₁ k := by
  fin_cases j' <;> fin_cases l'
  · show CM₀.gramRead (Φ₁ 0) (Φ₁ 0) = (GRep₁ 0 0).sum fun k a => C a * Φ₁ k
    rw [show Φ₁ 0 = 1 from rfl, show GRep₁ 0 0 = 0 from rfl,
      Finsupp.sum_zero_index]
    exact gramOp_one_left _ _
  · show CM₀.gramRead (Φ₁ 0) (Φ₁ 1) = (GRep₁ 0 1).sum fun k a => C a * Φ₁ k
    rw [show Φ₁ 0 = 1 from rfl, show GRep₁ 0 1 = 0 from rfl,
      Finsupp.sum_zero_index]
    exact gramOp_one_left _ _
  · show CM₀.gramRead (Φ₁ 1) (Φ₁ 0) = (GRep₁ 1 0).sum fun k a => C a * Φ₁ k
    rw [show Φ₁ 0 = 1 from rfl, show GRep₁ 1 0 = 0 from rfl,
      Finsupp.sum_zero_index]
    exact gramOp_one_right _ _
  · show CM₀.gramRead (Φ₁ 1) (Φ₁ 1) = (GRep₁ 1 1).sum fun k a => C a * Φ₁ k
    rw [show Φ₁ 1 = X 0 from rfl,
      show GRep₁ 1 1 = Finsupp.single 0 (49 : ℚ) from rfl,
      ColorModel.gramRead_X, Finsupp.sum_single_index (by simp)]
    show P₀.gram 0 0 = C 49 * Φ₁ 0
    rw [show Φ₁ 0 = 1 from rfl]
    unfold PolyProfile.gram P₀
    rw [Fin.sum_univ_one]
    rw [show (49 : ℚ) = 7 * 7 by norm_num, map_mul]
    ring

/-- The inner bag: `Bag(OU)` + death at rate 3, over dictionary
{count, colour-sum}. -/
@[reducible] noncomputable def B₁ : ColorModel (BagShape PUnit.{2}) (Fin 2) :=
  CM₀.bag Φ₁ (Fin 1) (fun _ => death₁) dRep₁ hdRep₁ GRep₁ hGRep₁

/-! ## Level 2: `Bag(Bag(OU))` with an outer death at rate γ = 5

Outer dictionary {1, k-pool, s-pool}: outer count, pooled inner count,
pooled inner colour-sum. **This is the closure in action: `B₁` — the
OUTPUT of one lift — re-enters as the color of the next.** -/

noncomputable def Φ₂ : Fin 3 → MvPolynomial (Fin 2) ℚ
  | 0 => 1
  | 1 => X 0
  | 2 => X 1

/-- The outer death edge: arity 1, no births, constant rate γ = 5 —
an entire inner net vanishes (the group-reading edge the μ-law's fence
excludes). -/
@[reducible] noncomputable def death₂ : B₁.BagEdge (Fin 3) Φ₂ where
  a := 1
  b := 0
  rate := C 5
  MixIx := PUnit
  w := fun _ => 1
  bStrat := fun _ p => p.elim0
  bg := fun _ p => p.elim0
  bKer := fun _ _ _ p => p.elim0
  hbKer := fun _ _ _ p => p.elim0

noncomputable def dRep₂ : Fin 3 → Fin 3 →₀ ℚ
  | 2 => Finsupp.single 2 (-2)
  | _ => 0

noncomputable def GRep₂ : Fin 3 → Fin 3 → Fin 3 →₀ ℚ
  | 2, 2 => Finsupp.single 1 49
  | _, _ => 0

theorem hdRep₂ (j' : Fin 3) :
    B₁.contRead (Φ₂ j') = (dRep₂ j').sum fun k a => C a * Φ₂ k := by
  fin_cases j'
  · show B₁.contRead (Φ₂ 0) = (dRep₂ 0).sum fun k a => C a * Φ₂ k
    rw [show Φ₂ 0 = 1 from rfl, show dRep₂ 0 = 0 from rfl,
      Finsupp.sum_zero_index]
    exact contOp_one _ _
  · show B₁.contRead (Φ₂ 1) = (dRep₂ 1).sum fun k a => C a * Φ₂ k
    rw [show Φ₂ 1 = X 0 from rfl, show dRep₂ 1 = 0 from rfl,
      Finsupp.sum_zero_index, ColorModel.contRead_X]
    show (dRep₁ 0).sum (fun k a => C a * X k) = 0
    rw [show dRep₁ 0 = 0 from rfl, Finsupp.sum_zero_index]
  · show B₁.contRead (Φ₂ 2) = (dRep₂ 2).sum fun k a => C a * Φ₂ k
    rw [show Φ₂ 2 = X 1 from rfl,
      show dRep₂ 2 = Finsupp.single 2 (-2 : ℚ) from rfl,
      ColorModel.contRead_X, Finsupp.sum_single_index (by simp)]
    show (dRep₁ 1).sum (fun k a => C a * X k) = C (-2) * Φ₂ 2
    rw [show dRep₁ 1 = Finsupp.single 1 (-2 : ℚ) from rfl,
      Finsupp.sum_single_index (by simp)]
    rfl

theorem hGRep₂ (j' l' : Fin 3) :
    B₁.gramRead (Φ₂ j') (Φ₂ l') = (GRep₂ j' l').sum fun k a => C a * Φ₂ k := by
  fin_cases j' <;> fin_cases l'
  · show B₁.gramRead (Φ₂ 0) (Φ₂ 0) = (GRep₂ 0 0).sum fun k a => C a * Φ₂ k
    rw [show Φ₂ 0 = 1 from rfl, show GRep₂ 0 0 = 0 from rfl,
      Finsupp.sum_zero_index]
    exact gramOp_one_left _ _
  · show B₁.gramRead (Φ₂ 0) (Φ₂ 1) = (GRep₂ 0 1).sum fun k a => C a * Φ₂ k
    rw [show Φ₂ 0 = 1 from rfl, show GRep₂ 0 1 = 0 from rfl,
      Finsupp.sum_zero_index]
    exact gramOp_one_left _ _
  · show B₁.gramRead (Φ₂ 0) (Φ₂ 2) = (GRep₂ 0 2).sum fun k a => C a * Φ₂ k
    rw [show Φ₂ 0 = 1 from rfl, show GRep₂ 0 2 = 0 from rfl,
      Finsupp.sum_zero_index]
    exact gramOp_one_left _ _
  · show B₁.gramRead (Φ₂ 1) (Φ₂ 0) = (GRep₂ 1 0).sum fun k a => C a * Φ₂ k
    rw [show Φ₂ 0 = 1 from rfl, show GRep₂ 1 0 = 0 from rfl,
      Finsupp.sum_zero_index]
    exact gramOp_one_right _ _
  · show B₁.gramRead (Φ₂ 1) (Φ₂ 1) = (GRep₂ 1 1).sum fun k a => C a * Φ₂ k
    rw [show Φ₂ 1 = X 0 from rfl, show GRep₂ 1 1 = 0 from rfl,
      Finsupp.sum_zero_index, ColorModel.gramRead_X]
    show (GRep₁ 0 0).sum (fun k a => C a * X k) = 0
    rw [show GRep₁ 0 0 = 0 from rfl, Finsupp.sum_zero_index]
  · show B₁.gramRead (Φ₂ 1) (Φ₂ 2) = (GRep₂ 1 2).sum fun k a => C a * Φ₂ k
    rw [show Φ₂ 1 = X 0 from rfl, show Φ₂ 2 = X 1 from rfl,
      show GRep₂ 1 2 = 0 from rfl, Finsupp.sum_zero_index,
      ColorModel.gramRead_X]
    show (GRep₁ 0 1).sum (fun k a => C a * X k) = 0
    rw [show GRep₁ 0 1 = 0 from rfl, Finsupp.sum_zero_index]
  · show B₁.gramRead (Φ₂ 2) (Φ₂ 0) = (GRep₂ 2 0).sum fun k a => C a * Φ₂ k
    rw [show Φ₂ 0 = 1 from rfl, show GRep₂ 2 0 = 0 from rfl,
      Finsupp.sum_zero_index]
    exact gramOp_one_right _ _
  · show B₁.gramRead (Φ₂ 2) (Φ₂ 1) = (GRep₂ 2 1).sum fun k a => C a * Φ₂ k
    rw [show Φ₂ 2 = X 1 from rfl, show Φ₂ 1 = X 0 from rfl,
      show GRep₂ 2 1 = 0 from rfl, Finsupp.sum_zero_index,
      ColorModel.gramRead_X]
    show (GRep₁ 1 0).sum (fun k a => C a * X k) = 0
    rw [show GRep₁ 1 0 = 0 from rfl, Finsupp.sum_zero_index]
  · show B₁.gramRead (Φ₂ 2) (Φ₂ 2) = (GRep₂ 2 2).sum fun k a => C a * Φ₂ k
    rw [show Φ₂ 2 = X 1 from rfl,
      show GRep₂ 2 2 = Finsupp.single 1 (49 : ℚ) from rfl,
      ColorModel.gramRead_X, Finsupp.sum_single_index (by simp)]
    show (GRep₁ 1 1).sum (fun k a => C a * X k) = C 49 * Φ₂ 1
    rw [show GRep₁ 1 1 = Finsupp.single 0 (49 : ℚ) from rfl,
      Finsupp.sum_single_index (by simp)]
    rfl

/-- **The two-level system**: the lift applied to the lift's output. -/
@[reducible] noncomputable def B₂ : ColorModel (BagShape (BagShape PUnit.{2})) (Fin 3) :=
  B₁.bag Φ₂ (Fin 1) (fun _ => death₂) dRep₂ hdRep₂ GRep₂ hGRep₂

/-! ## The concrete mode (K = 2; n₁ = 1, n₂ = 2) — the fixture cell -/

@[reducible] def inner1 : BagShape PUnit.{2} where
  T := Fin 1
  strat := fun _ => PUnit.unit

@[reducible] def inner2 : BagShape PUnit.{2} where
  T := Fin 2
  strat := fun _ => PUnit.unit

@[reducible] def S2cStrat : Fin 2 → BagShape PUnit.{2}
  | 0 => inner1
  | 1 => inner2

@[reducible] def S2c : BagShape (BagShape PUnit.{2}) where
  T := Fin 2
  strat := S2cStrat

/-- Splitting a sum over a sigma type (generic simp face). -/
theorem sum_sigma_univ {α : Type} [Fintype α] {β : α → Type}
    [∀ a, Fintype (β a)] {A : Type*} [AddCommMonoid A]
    (f : (Σ a, β a) → A) : ∑ x : Σ a, β a, f x = ∑ a, ∑ b, f ⟨a, b⟩ := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]

/-! ### The closed-form evaluations

A first evaluation route hit a structural wall: `simp`-unfolding of
the model literals mixed reduced and projected type-spellings inside
one application, after which simp congruence stalled at instance
transparency. This is the documented successor route: defeq-typed
lemmas at
projected spellings — every jump face evaluated structurally through
the pool-shift engine (`bind₁_jumpKer_poolC`), simp never touching a
model literal. Spelling discipline: `Fin`-ascribed literals, dictionary
reads at `X`-spellings, `C`-constants normalized by
`map_neg`/`map_ofNat` before the closing `ring`. -/

/-- The flat token variables at the mode, through the `tokEmb`
vocabulary (whose instances resolve at the `ColorModel` projection
level): `flatX t k` is the OU coordinate of inner token `k` of outer
token `t`. -/
noncomputable def flatX (t : Fin 2) (k : (S2cStrat t).T) :
    MvPolynomial (B₂.st S2c) ℚ :=
  B₁.tokEmb S2c t (CM₀.tokEmb (S2cStrat t) k (X 0))

/-! ## Evaluation helpers: leg addresses, retype bridges, closed rates,
pooled reads

The retype bridges (`iA`, `iB`, `e₁`, `cA`, `cB`, `ℓKA`, `ℓKB`) are the
load-bearing move of route (a): a value of projected type sitting in a
model-typed position is well-typed only at default transparency, which
aborts `kabstract`'s traversal ("target not type-correct under
instances"); a `@[reducible]` bridge is structurally well-typed at
every transparency while remaining definitionally the identity.
Second discipline: heterogeneously-spelled operands never meet a bare
binop — the odd leaf carries a type ascription. Third: `rw` runs only
inside level-homogeneous contexts; cross-level gluing is
`congrArg`/`trans`/`exact` (term-level defeq). -/

/-- The lifted inner-death leg of `B₂` (rate ρ = 3). -/
@[reducible] def ℓA : B₂.LegIx := Sum.inl (Sum.inr (Sum.inl 0))

/-- The outer-death leg of `B₂` (rate γ = 5). -/
@[reducible] def ℓB : B₂.LegIx := Sum.inr (Sum.inl 0)

/-- The lifted kill-promotion leg (rate = the atomic kill = 0). -/
@[reducible] def ℓKA : B₂.LegIx := Sum.inl (Sum.inr (Sum.inr ()))

/-- The outer kill-promotion leg (rate = `B₁.pKill` = 0). -/
@[reducible] def ℓKB : B₂.LegIx := Sum.inr (Sum.inr ())

/-- Retype bridge: a host token and an inner embedding form a lifted
inner-death instance. -/
@[reducible] def iA (t : Fin 2) (e : Fin 1 ↪ (S2cStrat t).T) :
    B₂.Inst ℓA S2c := ⟨t, e⟩

/-- Retype bridge: an outer-token selection is an outer-death
instance. -/
@[reducible] def iB (e : Fin 1 ↪ Fin 2) : B₂.Inst ℓB S2c := e

/-- Retype bridge: an inner-token selection is a `B₁` death-edge
instance at its host's stratum. -/
@[reducible] def e₁ (t : Fin 2) (e : Fin 1 ↪ (S2cStrat t).T) :
    B₁.Inst (Sum.inr (Sum.inl 0)) (S2cStrat t) := e

/-- Retype bridge: the unique mixture component of the lifted
inner-death leg. -/
@[reducible] def cA : B₂.legMix ℓA := PUnit.unit

/-- Retype bridge: the unique mixture component of the outer-death
leg. -/
@[reducible] def cB : B₂.legMix ℓB := PUnit.unit

/-- Value bridge: the pooled colour-sum, typed at the two-level flat
state by signature (so every op-tree over it is spelling-homogeneous).
-/
@[reducible] noncomputable def poolX : MvPolynomial (B₂.st S2c) ℚ :=
  B₁.poolC S2c (X 1)

/-- Value bridge: outer token `t`'s colour-sum read, at the two-level
flat state. -/
@[reducible] noncomputable def sumX (t : Fin 2) : MvPolynomial (B₂.st S2c) ℚ :=
  B₁.tokEmb S2c t (bind₁ (B₁.χ (S2c.strat t)) (X 1))

/-- Value bridge: inner token `k`'s OU coordinate at stratum
`S2cStrat t`, typed at `B₁`'s flat state. -/
@[reducible] noncomputable def tokX (t : Fin 2) (k : (S2cStrat t).T) :
    MvPolynomial (B₁.st (S2c.strat t)) ℚ :=
  CM₀.tokEmb (S2cStrat t) k (X 0)

/-- The lifted kill-promotion rate is zero (raw-spelled work stays
inside this lemma; the statement deposits a goal-spelled `0`). -/
theorem rateKA : B₂.legRate ℓKA = 0 := by
  show rename Sum.inl (rename Sum.inl (0 : MvPolynomial (Fin 1) ℚ)) = 0
  rw [map_zero, map_zero]

/-- The outer kill-promotion rate is zero. -/
theorem rateKB : B₂.legRate ℓKB = 0 := by
  show rename Sum.inl (0 : MvPolynomial (Fin 2) ℚ) = 0
  rw [map_zero]

theorem rateA : B₂.legRate ℓA = C 3 := by
  show rename Sum.inl (C 3 : MvPolynomial ((Fin 1 × Fin 1) ⊕ Fin 2) ℚ) = C 3
  rw [rename_C]

theorem rateB : B₂.legRate ℓB = C 5 := rfl

/-- Compiling the pooled colour-sum feature reads the pool of the
outer dictionary polynomial. -/
theorem compile_pool : bind₁ (B₂.χ S2c) (X 2) = poolX :=
  (bind₁_X_right (B₂.χ S2c) 2).trans rfl

/-- The colour-sum read of outer token 0, in `flatX` vocabulary. -/
theorem tokRead_zero : sumX 0 = flatX 0 (0 : Fin 1) := by
  show B₁.tokEmb S2c (0 : Fin 2) (bind₁ (B₁.χ (S2c.strat (0 : Fin 2))) (X 1))
    = flatX 0 (0 : Fin 1)
  have hpool : CM₀.poolC (S2cStrat 0) (X 0) = tokX 0 (0 : Fin 1) := by
    show (∑ k : Fin 1, CM₀.tokEmb (S2cStrat 0) k
        (bind₁ (CM₀.χ ((S2cStrat 0).strat k)) (X 0)))
      = tokX 0 (0 : Fin 1)
    have h1 : (∑ k : Fin 1, CM₀.tokEmb (S2cStrat 0) k
        (bind₁ (CM₀.χ ((S2cStrat 0).strat k)) (X 0)))
        = CM₀.tokEmb (S2cStrat 0) (0 : Fin 1)
            (bind₁ (CM₀.χ ((S2cStrat 0).strat (0 : Fin 1))) (X 0)) :=
      Fin.sum_univ_one _
    rw [h1, bind₁_X_right]
  rw [bind₁_X_right]
  exact (congrArg (B₁.tokEmb S2c (0 : Fin 2)) hpool).trans rfl

/-- The colour-sum read of outer token 1, in `flatX` vocabulary. -/
theorem tokRead_one : sumX 1 = flatX 1 (0 : Fin 2) + flatX 1 (1 : Fin 2) := by
  show B₁.tokEmb S2c (1 : Fin 2) (bind₁ (B₁.χ (S2c.strat (1 : Fin 2))) (X 1))
    = flatX 1 (0 : Fin 2) + flatX 1 (1 : Fin 2)
  have hpool : CM₀.poolC (S2cStrat 1) (X 0)
      = tokX 1 (0 : Fin 2) + tokX 1 (1 : Fin 2) := by
    show (∑ k : Fin 2, CM₀.tokEmb (S2cStrat 1) k
        (bind₁ (CM₀.χ ((S2cStrat 1).strat k)) (X 0)))
      = tokX 1 (0 : Fin 2) + tokX 1 (1 : Fin 2)
    have h1 : (∑ k : Fin 2, CM₀.tokEmb (S2cStrat 1) k
        (bind₁ (CM₀.χ ((S2cStrat 1).strat k)) (X 0)))
        = CM₀.tokEmb (S2cStrat 1) (0 : Fin 2)
            (bind₁ (CM₀.χ ((S2cStrat 1).strat (0 : Fin 2))) (X 0))
          + CM₀.tokEmb (S2cStrat 1) (1 : Fin 2)
              (bind₁ (CM₀.χ ((S2cStrat 1).strat (1 : Fin 2))) (X 0)) :=
      Fin.sum_univ_two _
    rw [h1, bind₁_X_right]
    rfl
  rw [bind₁_X_right]
  refine (congrArg (B₁.tokEmb S2c (1 : Fin 2)) hpool).trans ?_
  rw [map_add]
  rfl

/-- The pooled colour-sum, enumerated: `S_s` at the cell is the sum of
the three flat OU coordinates. -/
theorem pool_flatX :
    poolX = flatX 0 (0 : Fin 1) + (flatX 1 (0 : Fin 2) + flatX 1 (1 : Fin 2)) := by
  show (∑ t : Fin 2, B₁.tokEmb S2c t (bind₁ (B₁.χ (S2c.strat t)) (X 1)))
    = flatX 0 (0 : Fin 1) + (flatX 1 (0 : Fin 2) + flatX 1 (1 : Fin 2))
  refine (Fin.sum_univ_two _).trans ?_
  exact congrArg₂ (· + ·) tokRead_zero tokRead_one

/-! ## The pool-shift evaluations (route (a): every jump face through
the engine, at projected spellings) -/

/-- The inner engine at the dying token's stratum: transferring the
colour-sum across an inner death loses the dying token's colour. -/
theorem innerShift (t : Fin 2) (e : Fin 1 ↪ (S2cStrat t).T)
    (c : B₁.legMix (Sum.inr (Sum.inl 0))) :
    bind₁ (B₁.instKer (ℓ := Sum.inr (Sum.inl 0)) (s := S2cStrat t) (e₁ t e) c)
        (bind₁ (B₁.χ (B₁.instTgt (ℓ := Sum.inr (Sum.inl 0)) (s := S2cStrat t)
          (e₁ t e) c)) (X 1))
      = bind₁ (B₁.χ (S2c.strat t)) (X 1) - tokX t (e 0) := by
  rw [bind₁_X_right, bind₁_X_right]
  have hstep := CM₀.bind₁_jumpKer_poolC (S2cStrat t) e
    (fun p : Fin 0 => death₁.bStrat c p)
    (fun p : Fin 0 => death₁.bKer (S2cStrat t) e c p) (X 0)
  have h2 : (∑ r : Fin 1, CM₀.tokEmb (S2cStrat t) (e r)
        (bind₁ (CM₀.χ ((S2cStrat t).strat (e r))) (X 0)))
      = CM₀.tokEmb (S2cStrat t) (e 0)
          (bind₁ (CM₀.χ ((S2cStrat t).strat (e 0))) (X 0)) :=
    Fin.sum_univ_one _
  rw [Fin.sum_univ_zero, add_zero, h2, bind₁_X_right] at hstep
  exact hstep

/-- The born-token read of the lifted inner death: the surviving inner
pool, embedded at the host outer token. -/
theorem bornRead (t : Fin 2) (e : Fin 1 ↪ (S2cStrat t).T) (c : PUnit.{1}) :
    bind₁ (fun x => B₁.tokEmb S2c t
        (B₁.instKer (ℓ := Sum.inr (Sum.inl 0)) (s := S2cStrat t) (e₁ t e) c x))
      (bind₁ (B₁.χ (B₁.instTgt (ℓ := Sum.inr (Sum.inl 0)) (s := S2cStrat t)
        (e₁ t e) c)) (X 1))
      = sumX t - flatX t (e 0) := by
  refine (B₁.bind₁_tokEmb_comp S2c t _ _).trans ?_
  refine (congrArg (B₁.tokEmb S2c t) (innerShift t e c)).trans ?_
  rw [map_sub,
    show B₁.tokEmb S2c t (tokX t (e 0)) = flatX t (e 0) from rfl]
  rfl

/-- The outer engine, lifted-inner-death face: the two-level transfer
of the pooled colour-sum loses exactly the dying token's flat
coordinate. -/
theorem kerCore (t : Fin 2) (e : Fin 1 ↪ (S2cStrat t).T) (c : PUnit.{1}) :
    bind₁ (B₁.jumpKer S2c (singleEmb t)
        (fun _ : Fin 1 => fun x => B₁.tokEmb S2c t
          (B₁.instKer (ℓ := Sum.inr (Sum.inl 0)) (s := S2cStrat t) (e₁ t e) c x)))
      (B₁.poolC (jumpShape S2c (singleEmb t)
        (fun _ : Fin 1 => B₁.instTgt (ℓ := Sum.inr (Sum.inl 0))
          (s := S2cStrat t) (e₁ t e) c)) (X 1))
      = poolX - flatX t (e 0) := by
  have hstep := B₁.bind₁_jumpKer_poolC_single S2c t
    (fun _ : Fin 1 => B₁.instTgt (ℓ := Sum.inr (Sum.inl 0)) (s := S2cStrat t)
      (e₁ t e) c)
    (fun _ : Fin 1 => fun x => B₁.tokEmb S2c t
      (B₁.instKer (ℓ := Sum.inr (Sum.inl 0)) (s := S2cStrat t) (e₁ t e) c x))
    (X 1)
  have h2 : (∑ p : Fin 1, bind₁
        ((fun _ : Fin 1 => fun x => B₁.tokEmb S2c t
          (B₁.instKer (ℓ := Sum.inr (Sum.inl 0)) (s := S2cStrat t) (e₁ t e) c x)) p)
        (bind₁ (B₁.χ ((fun _ : Fin 1 => B₁.instTgt (ℓ := Sum.inr (Sum.inl 0))
          (s := S2cStrat t) (e₁ t e) c) p)) (X 1)))
      = bind₁ (fun x => B₁.tokEmb S2c t
          (B₁.instKer (ℓ := Sum.inr (Sum.inl 0)) (s := S2cStrat t) (e₁ t e) c x))
        (bind₁ (B₁.χ (B₁.instTgt (ℓ := Sum.inr (Sum.inl 0)) (s := S2cStrat t)
          (e₁ t e) c)) (X 1)) :=
    Fin.sum_univ_one _
  rw [h2, bornRead t e c] at hstep
  refine hstep.trans ?_
  show poolX - sumX t + (sumX t - flatX t (e 0)) = poolX - flatX t (e 0)
  ring

/-- The two-level transfer of the pooled colour-sum along the lifted
inner-death instance at outer token `t`, dying token `e 0`. -/
theorem kerA (t : Fin 2) (e : Fin 1 ↪ (S2cStrat t).T) (c : B₂.legMix ℓA) :
    bind₁ (B₂.instKer (ℓ := ℓA) (s := S2c) (iA t e) c)
        (bind₁ (B₂.χ (B₂.instTgt (ℓ := ℓA) (s := S2c) (iA t e) c)) (X 2))
      = poolX - flatX t (e 0) := by
  rw [bind₁_X_right]
  exact kerCore t e c

/-- The transfer along the outer-death instance at outer token `e 0`:
the pooled colour-sum loses the whole inner net's read. -/
theorem kerB (e : Fin 1 ↪ Fin 2) (c : B₂.legMix ℓB) :
    bind₁ (B₂.instKer (ℓ := ℓB) (s := S2c) (iB e) c)
        (bind₁ (B₂.χ (B₂.instTgt (ℓ := ℓB) (s := S2c) (iB e) c)) (X 2))
      = poolX - sumX (e 0) := by
  rw [bind₁_X_right]
  have hstep := B₁.bind₁_jumpKer_poolC S2c e
    (fun p : Fin 0 => death₂.bStrat c p)
    (fun p : Fin 0 => death₂.bKer S2c e c p) (X 1)
  have h2 : (∑ r : Fin 1, B₁.tokEmb S2c (e r)
        (bind₁ (B₁.χ (S2c.strat (e r))) (X 1)))
      = B₁.tokEmb S2c (e 0) (bind₁ (B₁.χ (S2c.strat (e 0))) (X 1)) :=
    Fin.sum_univ_one _
  rw [Fin.sum_univ_zero, add_zero, h2] at hstep
  exact hstep

/-! ## The jump terms, per instance and enumerated -/

/-- Flat jump of one lifted inner-death instance on `S_s`. -/
theorem jumpA (t : Fin 2) (e : Fin 1 ↪ (S2cStrat t).T) :
    B₂.flatJump (ℓ := ℓA) (s := S2c) (iA t e) (X 2)
      = C 3 * ((poolX - flatX t (e 0)) - poolX) := by
  unfold ColorModel.flatJump
  rw [rateA, bind₁_C_right, compile_pool]
  have hmix : (∑ c, C (B₂.legW ℓA c)
        * bind₁ (B₂.instKer (ℓ := ℓA) (s := S2c) (iA t e) c)
            (bind₁ (B₂.χ (B₂.instTgt (ℓ := ℓA) (s := S2c) (iA t e) c)) (X 2)))
      = poolX - flatX t (e 0) := by
    refine (Finset.sum_eq_single_of_mem cA (Finset.mem_univ _)
      (fun b _ hb => absurd
        (@Subsingleton.elim _ (inferInstanceAs (Subsingleton PUnit.{1})) b cA)
        hb)).trans ?_
    show C (B₂.legW ℓA cA)
        * bind₁ (B₂.instKer (ℓ := ℓA) (s := S2c) (iA t e) cA)
            (bind₁ (B₂.χ (B₂.instTgt (ℓ := ℓA) (s := S2c) (iA t e) cA)) (X 2))
      = poolX - flatX t (e 0)
    rw [show B₂.legW ℓA cA = (1 : ℚ) from rfl, C_1, one_mul]
    exact kerA t e cA
  rw [hmix]

/-- Flat jump of one outer-death instance on `S_s`. -/
theorem jumpB (e : Fin 1 ↪ Fin 2) :
    B₂.flatJump (ℓ := ℓB) (s := S2c) (iB e) (X 2)
      = C 5 * ((poolX - sumX (e 0)) - poolX) := by
  unfold ColorModel.flatJump
  rw [rateB, bind₁_C_right, compile_pool]
  have hmix : (∑ c, C (B₂.legW ℓB c)
        * bind₁ (B₂.instKer (ℓ := ℓB) (s := S2c) (iB e) c)
            (bind₁ (B₂.χ (B₂.instTgt (ℓ := ℓB) (s := S2c) (iB e) c)) (X 2)))
      = poolX - sumX (e 0) := by
    refine (Finset.sum_eq_single_of_mem cB (Finset.mem_univ _)
      (fun b _ hb => absurd
        (@Subsingleton.elim _ (inferInstanceAs (Subsingleton PUnit.{1})) b cB)
        hb)).trans ?_
    show C (B₂.legW ℓB cB)
        * bind₁ (B₂.instKer (ℓ := ℓB) (s := S2c) (iB e) cB)
            (bind₁ (B₂.χ (B₂.instTgt (ℓ := ℓB) (s := S2c) (iB e) cB)) (X 2))
      = poolX - sumX (e 0)
    rw [show B₂.legW ℓB cB = (1 : ℚ) from rfl, C_1, one_mul]
    exact kerB e cB
  rw [hmix]

/-- The lifted kill-promotion leg carries the atomic colour's kill rate
— which is zero. -/
theorem jumpKillLift (i : B₂.Inst ℓKA S2c) (q : MvPolynomial (Fin 3) ℚ) :
    B₂.flatJump (s := S2c) i q = 0 := by
  unfold ColorModel.flatJump
  rw [rateKA, map_zero, zero_mul]

/-- The outer kill-promotion leg carries `B₁.pKill = 0` (the lift is
conservative). -/
theorem jumpKillOuter (i : B₂.Inst ℓKB S2c) (q : MvPolynomial (Fin 3) ℚ) :
    B₂.flatJump (s := S2c) i q = 0 := by
  unfold ColorModel.flatJump
  rw [rateKB, map_zero, zero_mul]

/-- Enumerating a sum over the lifted-inner-death instance family:
one term per living inner token. -/
theorem sumA {A : Type*} [AddCommMonoid A]
    (F : ((t : Fin 2) × (Fin 1 ↪ (S2cStrat t).T)) → A) :
    (∑ i, F i)
      = F ⟨0, singleEmb (0 : Fin 1)⟩
        + (F ⟨1, singleEmb (0 : Fin 2)⟩ + F ⟨1, singleEmb (1 : Fin 2)⟩) := by
  rw [sum_sigma_univ]
  calc (∑ t : Fin 2, ∑ e : Fin 1 ↪ (S2cStrat t).T, F ⟨t, e⟩)
      = (∑ e : Fin 1 ↪ (S2cStrat 0).T, F ⟨0, e⟩)
        + ∑ e : Fin 1 ↪ (S2cStrat 1).T, F ⟨1, e⟩ := Fin.sum_univ_two _
    _ = (∑ k : (S2cStrat 0).T, F ⟨0, singleEmb k⟩)
        + ∑ k : (S2cStrat 1).T, F ⟨1, singleEmb k⟩ := by
        rw [sum_emb_fin_one fun e => F ⟨0, e⟩, sum_emb_fin_one fun e => F ⟨1, e⟩]
    _ = (∑ k : Fin 1, F ⟨0, singleEmb k⟩) + ∑ k : Fin 2, F ⟨1, singleEmb k⟩ :=
        rfl
    _ = F ⟨0, singleEmb (0 : Fin 1)⟩
        + (F ⟨1, singleEmb (0 : Fin 2)⟩ + F ⟨1, singleEmb (1 : Fin 2)⟩) := by
        rw [Fin.sum_univ_one, Fin.sum_univ_two]

/-- Enumerating a sum over the outer-death instance family: one term
per outer token. -/
theorem sumB {A : Type*} [AddCommMonoid A] (F : (Fin 1 ↪ Fin 2) → A) :
    (∑ e, F e) = F (singleEmb (0 : Fin 2)) + F (singleEmb (1 : Fin 2)) := by
  rw [sum_emb_fin_one F]
  exact Fin.sum_univ_two _

/-- The instance-jump sum of `B₂` at the cell, enumerated: only the two
death legs contribute — one instance per living inner token (ρ-leg),
one per outer token (γ-leg). -/
theorem jumpSum (q : MvPolynomial (Fin 3) ℚ) :
    (∑ ℓ, ∑ i : B₂.Inst ℓ S2c, B₂.flatJump i q)
      = (B₂.flatJump (ℓ := ℓA) (s := S2c) (iA 0 (singleEmb (0 : Fin 1))) q
          + (B₂.flatJump (ℓ := ℓA) (s := S2c) (iA 1 (singleEmb (0 : Fin 2))) q
            + B₂.flatJump (ℓ := ℓA) (s := S2c) (iA 1 (singleEmb (1 : Fin 2))) q))
        + (B₂.flatJump (ℓ := ℓB) (s := S2c) (iB (singleEmb (0 : Fin 2))) q
          + B₂.flatJump (ℓ := ℓB) (s := S2c) (iB (singleEmb (1 : Fin 2))) q) := by
  have hz : ∀ ℓ' ∈ (Finset.univ : Finset B₂.LegIx), ℓ' ≠ ℓA ∧ ℓ' ≠ ℓB →
      (∑ i : B₂.Inst ℓ' S2c, B₂.flatJump i q) = 0 := by
    intro ℓ' _ h
    exact match ℓ', h with
      | .inl (.inl x), _ => x.elim0
      | .inl (.inr (.inl ε)), h =>
          absurd (congrArg
            (fun z => (Sum.inl (Sum.inr (Sum.inl z)) : B₂.LegIx))
            (Subsingleton.elim ε 0)) h.1
      | .inl (.inr (.inr u)), _ =>
          Finset.sum_eq_zero fun i _ => jumpKillLift i q
      | .inr (.inl ε), h =>
          absurd (congrArg
            (fun z => (Sum.inr (Sum.inl z) : B₂.LegIx))
            (Subsingleton.elim ε 0)) h.2
      | .inr (.inr u), _ =>
          Finset.sum_eq_zero fun i _ => jumpKillOuter i q
  have hne : ℓA ≠ ℓB := fun hAB => by
    have h' : (Sum.inl (Sum.inr (Sum.inl 0)) : B₁.LegIx ⊕ (Fin 1 ⊕ Unit))
        = Sum.inr (Sum.inl 0) := hAB
    exact Sum.inl_ne_inr h'
  have hA : (∑ i : B₂.Inst ℓA S2c, B₂.flatJump i q)
      = B₂.flatJump (ℓ := ℓA) (s := S2c) (iA 0 (singleEmb (0 : Fin 1))) q
        + (B₂.flatJump (ℓ := ℓA) (s := S2c) (iA 1 (singleEmb (0 : Fin 2))) q
          + B₂.flatJump (ℓ := ℓA) (s := S2c) (iA 1 (singleEmb (1 : Fin 2))) q) := by
    show (∑ i : (t : Fin 2) × (Fin 1 ↪ (S2cStrat t).T),
        B₂.flatJump (ℓ := ℓA) (s := S2c) (iA i.1 i.2) q) = _
    exact sumA fun i => B₂.flatJump (ℓ := ℓA) (s := S2c) (iA i.1 i.2) q
  have hB : (∑ i : B₂.Inst ℓB S2c, B₂.flatJump i q)
      = B₂.flatJump (ℓ := ℓB) (s := S2c) (iB (singleEmb (0 : Fin 2))) q
        + B₂.flatJump (ℓ := ℓB) (s := S2c) (iB (singleEmb (1 : Fin 2))) q := by
    show (∑ e : Fin 1 ↪ Fin 2, B₂.flatJump (ℓ := ℓB) (s := S2c) (iB e) q) = _
    exact sumB fun e => B₂.flatJump (ℓ := ℓB) (s := S2c) (iB e) q
  refine (Finset.sum_eq_add_of_mem ℓA ℓB (Finset.mem_univ _)
    (Finset.mem_univ _) hne hz).trans ?_
  exact congrArg₂ (· + ·) hA hB

/-! ## The boxed identities at the fixture cell -/

/-- **The boxed identity for V = S_s** at mode
(K = 2; n₁ = 1, n₂ = 2): the two-level flat generator of the pooled
colour-sum is −(a+ρ+γ) = −10 times it. At a concrete mode the flat
generator IS the explicit-token (flattened) generator, so this is
simultaneously the cell check. -/
theorem twoLevel_V :
    B₂.flatGen S2c (X 2) = C (-10) * bind₁ (B₂.χ S2c) (X 2) := by
  have hd : B₂.pDrift 2 = C (-2) * X 2 := by
    show ((dRep₂ 2).sum fun k a => C a * X k) = C (-2) * X 2
    rw [show dRep₂ 2 = Finsupp.single 2 (-2 : ℚ) from rfl,
      Finsupp.sum_single_index (by simp)]
  show contOp (B₂.fDrift S2c) (B₂.fGram S2c) (bind₁ (B₂.χ S2c) (X 2))
      - B₂.fKill S2c * bind₁ (B₂.χ S2c) (X 2)
      + (∑ ℓ, ∑ i : B₂.Inst ℓ S2c, B₂.flatJump i (X 2))
    = C (-10) * bind₁ (B₂.χ S2c) (X 2)
  rw [contOp_compile (B₂.fDrift S2c) (B₂.fGram S2c) (B₂.χ S2c) B₂.pDrift
      B₂.pGram (B₂.hDrift S2c) (B₂.hGram S2c) (X 2), contOp_X, hd,
    algHom_C_mul, show B₂.fKill S2c = 0 from rfl, zero_mul, sub_zero,
    jumpSum,
    jumpA 0 (singleEmb (0 : Fin 1)), jumpA 1 (singleEmb (0 : Fin 2)),
    jumpA 1 (singleEmb (1 : Fin 2)),
    jumpB (singleEmb (0 : Fin 2)), jumpB (singleEmb (1 : Fin 2)),
    show singleEmb (0 : Fin 1) 0 = (0 : Fin 1) from rfl,
    show singleEmb (0 : Fin 2) 0 = (0 : Fin 2) from rfl,
    show singleEmb (1 : Fin 2) 0 = (1 : Fin 2) from rfl,
    tokRead_zero, tokRead_one, compile_pool, pool_flatX]
  simp only [map_neg, map_ofNat]
  ring

/-- The presentation-level continuous reading of `S_s²`: drift pairs
the gradient (−2·2·S_s²-direction), the gram contributes the σ²-count
through the Hessian — all at feature coordinates (`Fin 3`), where simp
is safe (no model literals). -/
theorem contReadW :
    contOp B₂.pDrift B₂.pGram ((X 2 : MvPolynomial (Fin 3) ℚ) * X 2)
      = C (-4) * (X 2 * X 2) + C 49 * X 1 := by
  unfold contOp
  simp [ColorModel.bag_pDrift, ColorModel.bag_pGram, dRep₂, GRep₂,
    Fin.sum_univ_three, pderiv_X, Pi.single_apply,
    Finsupp.sum_single_index, Finsupp.sum_zero_index]
  have hneg : ((-Finsupp.single 2 2 : Fin 3 →₀ ℚ).sum
        fun k a => (C a * X k : MvPolynomial (Fin 3) ℚ))
      = C (-2) * X 2 := by
    rw [show (-Finsupp.single 2 2 : Fin 3 →₀ ℚ) = Finsupp.single 2 (-2 : ℚ)
        from (Finsupp.single_neg 2 (2 : ℚ)).symm,
      Finsupp.sum_single_index (by simp)]
  rw [hneg]
  simp only [map_neg, map_ofNat]
  have h2 : (2 : MvPolynomial (Fin 3) ℚ) * C (2⁻¹ : ℚ) = 1 := by
    rw [show (2 : MvPolynomial (Fin 3) ℚ) = C (2 : ℚ)
        from (map_ofNat C 2).symm, ← map_mul,
      show (2 * 2⁻¹ : ℚ) = 1 from by norm_num, C_1]
  linear_combination (49 * X 1 : MvPolynomial (Fin 3) ℚ) * h2

/-- Compiling `S_s²` squares the pooled colour-sum. -/
theorem compile_pool_sq :
    bind₁ (B₂.χ S2c) ((X 2 : MvPolynomial (Fin 3) ℚ) * X 2)
      = poolX * poolX := by
  rw [map_mul, compile_pool]

/-- Flat jump of one lifted inner-death instance on `S_s²`. -/
theorem jumpA_W (t : Fin 2) (e : Fin 1 ↪ (S2cStrat t).T) :
    B₂.flatJump (ℓ := ℓA) (s := S2c) (iA t e) (X 2 * X 2)
      = C 3 * ((poolX - flatX t (e 0)) * (poolX - flatX t (e 0))
          - poolX * poolX) := by
  unfold ColorModel.flatJump
  rw [rateA, bind₁_C_right, compile_pool_sq]
  have hmix : (∑ c, C (B₂.legW ℓA c)
        * bind₁ (B₂.instKer (ℓ := ℓA) (s := S2c) (iA t e) c)
            (bind₁ (B₂.χ (B₂.instTgt (ℓ := ℓA) (s := S2c) (iA t e) c))
              (X 2 * X 2)))
      = (poolX - flatX t (e 0)) * (poolX - flatX t (e 0)) := by
    refine (Finset.sum_eq_single_of_mem cA (Finset.mem_univ _)
      (fun b _ hb => absurd
        (@Subsingleton.elim _ (inferInstanceAs (Subsingleton PUnit.{1})) b cA)
        hb)).trans ?_
    show C (B₂.legW ℓA cA)
        * bind₁ (B₂.instKer (ℓ := ℓA) (s := S2c) (iA t e) cA)
            (bind₁ (B₂.χ (B₂.instTgt (ℓ := ℓA) (s := S2c) (iA t e) cA))
              (X 2 * X 2))
      = (poolX - flatX t (e 0)) * (poolX - flatX t (e 0))
    rw [show B₂.legW ℓA cA = (1 : ℚ) from rfl, C_1, one_mul, map_mul,
      map_mul, kerA t e cA]
  rw [hmix]

/-- Flat jump of one outer-death instance on `S_s²`. -/
theorem jumpB_W (e : Fin 1 ↪ Fin 2) :
    B₂.flatJump (ℓ := ℓB) (s := S2c) (iB e) (X 2 * X 2)
      = C 5 * ((poolX - sumX (e 0)) * (poolX - sumX (e 0))
          - poolX * poolX) := by
  unfold ColorModel.flatJump
  rw [rateB, bind₁_C_right, compile_pool_sq]
  have hmix : (∑ c, C (B₂.legW ℓB c)
        * bind₁ (B₂.instKer (ℓ := ℓB) (s := S2c) (iB e) c)
            (bind₁ (B₂.χ (B₂.instTgt (ℓ := ℓB) (s := S2c) (iB e) c))
              (X 2 * X 2)))
      = (poolX - sumX (e 0)) * (poolX - sumX (e 0)) := by
    refine (Finset.sum_eq_single_of_mem cB (Finset.mem_univ _)
      (fun b _ hb => absurd
        (@Subsingleton.elim _ (inferInstanceAs (Subsingleton PUnit.{1})) b cB)
        hb)).trans ?_
    show C (B₂.legW ℓB cB)
        * bind₁ (B₂.instKer (ℓ := ℓB) (s := S2c) (iB e) cB)
            (bind₁ (B₂.χ (B₂.instTgt (ℓ := ℓB) (s := S2c) (iB e) cB))
              (X 2 * X 2))
      = (poolX - sumX (e 0)) * (poolX - sumX (e 0))
    rw [show B₂.legW ℓB cB = (1 : ℚ) from rfl, C_1, one_mul, map_mul,
      map_mul, kerB e cB]
  rw [hmix]

/-- **The four-block boxed identity for W = S_s²** at the
same mode, including BOTH dictionary-growth species: with
$x_1$ the first inner net's token and $y_1, y_2$ the second's,
$S_{s_2} = x_1^2 + y_1^2 + y_2^2$ (inner mint, pooled through both
levels) and $S_{s^2} = x_1^2 + (y_1+y_2)^2$ (outer mint):
$\mathcal{A} S_s^2 = -2(a+\rho+\gamma) S_s^2 + \sigma^2 S_k
+ \rho S_{s_2} + \gamma S_{s^2}$, i.e. $-20 S_s^2 + 49 S_k + 3 S_{s_2}
+ 5 S_{s^2}$. -/
theorem twoLevel_W :
    B₂.flatGen S2c (X 2 * X 2)
      = C (-20) * (bind₁ (B₂.χ S2c) (X 2 * X 2))
        + C 49 * bind₁ (B₂.χ S2c) (X 1)
        + C 3 * (flatX 0 0 * flatX 0 0 + flatX 1 0 * flatX 1 0
            + flatX 1 1 * flatX 1 1)
        + C 5 * (flatX 0 0 * flatX 0 0
            + (flatX 1 0 + flatX 1 1) * (flatX 1 0 + flatX 1 1)) := by
  show contOp (B₂.fDrift S2c) (B₂.fGram S2c) (bind₁ (B₂.χ S2c) (X 2 * X 2))
      - B₂.fKill S2c * bind₁ (B₂.χ S2c) (X 2 * X 2)
      + (∑ ℓ, ∑ i : B₂.Inst ℓ S2c, B₂.flatJump i (X 2 * X 2))
    = _
  rw [contOp_compile (B₂.fDrift S2c) (B₂.fGram S2c) (B₂.χ S2c) B₂.pDrift
      B₂.pGram (B₂.hDrift S2c) (B₂.hGram S2c) (X 2 * X 2), contReadW,
    map_add, algHom_C_mul, algHom_C_mul,
    show B₂.fKill S2c = 0 from rfl, zero_mul, sub_zero,
    jumpSum,
    jumpA_W 0 (singleEmb (0 : Fin 1)), jumpA_W 1 (singleEmb (0 : Fin 2)),
    jumpA_W 1 (singleEmb (1 : Fin 2)),
    jumpB_W (singleEmb (0 : Fin 2)), jumpB_W (singleEmb (1 : Fin 2)),
    show singleEmb (0 : Fin 1) 0 = (0 : Fin 1) from rfl,
    show singleEmb (0 : Fin 2) 0 = (0 : Fin 2) from rfl,
    show singleEmb (1 : Fin 2) 0 = (1 : Fin 2) from rfl,
    tokRead_zero, tokRead_one, compile_pool_sq, pool_flatX]
  simp only [map_neg, map_ofNat]
  ring

/-- The polymorphic square, instantiated at the two-level fixture and
its cell: `bag_square` holds at `B₂`, `S2c`, and the S_s
certificate. (`twoLevel_V` above evaluates the closed form
−(a+ρ+γ)·S_s of the same generator.) -/
theorem twoLevel_square :
    B₂.flatGen S2c (X 2)
      = bind₁ (B₂.χ S2c)
          (B₂.contRead (X 2) - B₂.pKill * X 2)
        + ∑ ℓ, ∑ i : B₂.Inst ℓ S2c,
            bind₁ (Sum.elim (B₂.instHval i) (B₂.χ S2c))
              (B₂.dtRead ℓ (X 2)) :=
  ColorModel.models_square B₂ S2c (X 2)

/-! ## The γ = 0 μ-coherence law at the cell

The second lift at the μ*-pulled-back dictionary (`Φ = X`: each outer
feature the pool of an inner aggregate), with NO outer edges. The
closure witnesses are literally `dRep₁`/`GRep₁` again — the tower
feeds itself (the reps' correctness at the pulled-back dictionary is
`rfl` after `contRead_X`/`gramRead_X`, because the first lift's output
fields are linear by construction). -/

theorem hdRepμ (j' : Fin 2) :
    B₁.contRead ((X : Fin 2 → MvPolynomial (Fin 2) ℚ) j')
      = (dRep₁ j').sum fun k a => C a * (X : Fin 2 → MvPolynomial (Fin 2) ℚ) k := by
  rw [ColorModel.contRead_X]
  rfl

theorem hGRepμ (j' l' : Fin 2) :
    B₁.gramRead ((X : Fin 2 → MvPolynomial (Fin 2) ℚ) j')
        ((X : Fin 2 → MvPolynomial (Fin 2) ℚ) l')
      = (GRep₁ j' l').sum fun k a => C a * (X : Fin 2 → MvPolynomial (Fin 2) ℚ) k := by
  rw [ColorModel.gramRead_X]
  rfl

/-- The γ = 0 two-level system on the pulled-back dictionary: no outer
edges (the group-reading death is exactly what the μ-law's fence
excludes). -/
@[reducible] noncomputable def B₂γ0 :
    ColorModel (BagShape (BagShape PUnit.{2})) (Fin 2) :=
  B₁.bag (X : Fin 2 → MvPolynomial (Fin 2) ℚ) (Fin 0) (fun ε => ε.elim0)
    dRep₁ hdRepμ GRep₁ hGRepμ

/-! ### The μ-cell evaluation apparatus (same route (a) discipline:
bridges, goal-spelled rates, engine-evaluated jump faces; the pool
transport itself is the general `mu_compat_pool`) -/

/-- The lifted inner-death leg of the γ = 0 tower. -/
@[reducible] def ℓAμ : B₂γ0.LegIx := Sum.inl (Sum.inr (Sum.inl 0))

/-- The lifted kill-promotion leg of the γ = 0 tower (rate 0). -/
@[reducible] def ℓKAμ : B₂γ0.LegIx := Sum.inl (Sum.inr (Sum.inr ()))

/-- The outer kill-promotion leg of the γ = 0 tower (rate 0). -/
@[reducible] def ℓKBμ : B₂γ0.LegIx := Sum.inr (Sum.inr ())

/-- Retype bridge: instance of the lifted inner death in the γ = 0
tower. -/
@[reducible] def iAμ (t : Fin 2) (e : Fin 1 ↪ (S2cStrat t).T) :
    B₂γ0.Inst ℓAμ S2c := ⟨t, e⟩

/-- Retype bridge: the unique mixture component of `ℓAμ`. -/
@[reducible] def cAμ : B₂γ0.legMix ℓAμ := PUnit.unit

/-- The `B₁` death-edge leg (as seen at the flattened stratum). -/
@[reducible] def ℓF : B₁.LegIx := Sum.inr (Sum.inl 0)

/-- The `B₁` kill-promotion leg (rate 0). -/
@[reducible] def ℓKF : B₁.LegIx := Sum.inr (Sum.inr ())

/-- Retype bridge: a token selection at the flattened stratum is a
`B₁` death-edge instance there. -/
@[reducible] def iF (e : Fin 1 ↪ (ColorModel.muShape S2c).T) :
    B₁.Inst ℓF (ColorModel.muShape S2c) := e

/-- Retype bridge: the unique mixture component of `ℓF`. -/
@[reducible] def cF : B₁.legMix ℓF := PUnit.unit

/-- Value bridge: the pooled colour-sum, at the γ = 0 tower's flat
state. -/
@[reducible] noncomputable def poolXμ : MvPolynomial (B₂γ0.st S2c) ℚ :=
  B₁.poolC S2c (X 1)

/-- Value bridge: `flatX`, at the γ = 0 tower's flat state. -/
@[reducible] noncomputable def flatXμ (t : Fin 2) (k : (S2cStrat t).T) :
    MvPolynomial (B₂γ0.st S2c) ℚ := flatX t k

/-- Value bridge: the flattened-stratum pool of the OU coordinate. -/
@[reducible] noncomputable def poolF :
    MvPolynomial (B₁.st (ColorModel.muShape S2c)) ℚ :=
  CM₀.poolC (ColorModel.muShape S2c) (X 0)

/-- Value bridge: one flattened token's OU coordinate. -/
@[reducible] noncomputable def tokF (tk : (ColorModel.muShape S2c).T) :
    MvPolynomial (B₁.st (ColorModel.muShape S2c)) ℚ :=
  CM₀.tokEmb (ColorModel.muShape S2c) tk (X 0)

theorem rateAμ : B₂γ0.legRate ℓAμ = C 3 := by
  show rename Sum.inl (C 3 : MvPolynomial ((Fin 1 × Fin 1) ⊕ Fin 2) ℚ) = C 3
  rw [rename_C]

theorem rateKAμ : B₂γ0.legRate ℓKAμ = 0 := by
  show rename Sum.inl (rename Sum.inl (0 : MvPolynomial (Fin 1) ℚ)) = 0
  rw [map_zero, map_zero]

theorem rateKBμ : B₂γ0.legRate ℓKBμ = 0 := by
  show rename Sum.inl (0 : MvPolynomial (Fin 2) ℚ) = 0
  rw [map_zero]

theorem rateF : B₁.legRate ℓF = C 3 := rfl

theorem rateKF : B₁.legRate ℓKF = 0 := by
  show rename Sum.inl (0 : MvPolynomial (Fin 1) ℚ) = 0
  rw [map_zero]

/-- Compiling the pulled-back colour-sum feature at the tower. -/
theorem compile_poolμ :
    bind₁ (B₂γ0.χ S2c) ((X 1 : MvPolynomial (Fin 2) ℚ)) = poolXμ :=
  (bind₁_X_right (B₂γ0.χ S2c) 1).trans rfl

/-- Compiling the colour-sum feature at the flattened stratum. -/
theorem compile_poolF :
    bind₁ (B₁.χ (ColorModel.muShape S2c)) ((X 1 : MvPolynomial (Fin 2) ℚ))
      = poolF :=
  (bind₁_X_right (B₁.χ (ColorModel.muShape S2c)) 1).trans rfl

/-- The γ = 0 tower's inner-death transfer: `kerCore`, re-read at the
pulled-back dictionary (whose transfer kernels are the same). -/
theorem kerAμ (t : Fin 2) (e : Fin 1 ↪ (S2cStrat t).T) (c : B₂γ0.legMix ℓAμ) :
    bind₁ (B₂γ0.instKer (ℓ := ℓAμ) (s := S2c) (iAμ t e) c)
        (bind₁ (B₂γ0.χ (B₂γ0.instTgt (ℓ := ℓAμ) (s := S2c) (iAμ t e) c)) (X 1))
      = poolXμ - flatXμ t (e 0) := by
  rw [bind₁_X_right]
  exact kerCore t e c

/-- Flat jump of one lifted inner-death instance on the pulled-back
colour-sum, γ = 0 tower. -/
theorem jumpAμ (t : Fin 2) (e : Fin 1 ↪ (S2cStrat t).T) :
    B₂γ0.flatJump (ℓ := ℓAμ) (s := S2c) (iAμ t e) (X 1)
      = C 3 * ((poolXμ - flatXμ t (e 0)) - poolXμ) := by
  unfold ColorModel.flatJump
  rw [rateAμ, bind₁_C_right, compile_poolμ]
  have hmix : (∑ c, C (B₂γ0.legW ℓAμ c)
        * bind₁ (B₂γ0.instKer (ℓ := ℓAμ) (s := S2c) (iAμ t e) c)
            (bind₁ (B₂γ0.χ (B₂γ0.instTgt (ℓ := ℓAμ) (s := S2c) (iAμ t e) c))
              (X 1)))
      = poolXμ - flatXμ t (e 0) := by
    refine (Finset.sum_eq_single_of_mem cAμ (Finset.mem_univ _)
      (fun b _ hb => absurd
        (@Subsingleton.elim _ (inferInstanceAs (Subsingleton PUnit.{1})) b cAμ)
        hb)).trans ?_
    show C (B₂γ0.legW ℓAμ cAμ)
        * bind₁ (B₂γ0.instKer (ℓ := ℓAμ) (s := S2c) (iAμ t e) cAμ)
            (bind₁ (B₂γ0.χ (B₂γ0.instTgt (ℓ := ℓAμ) (s := S2c) (iAμ t e) cAμ))
              (X 1))
      = poolXμ - flatXμ t (e 0)
    rw [show B₂γ0.legW ℓAμ cAμ = (1 : ℚ) from rfl, C_1, one_mul]
    exact kerAμ t e cAμ
  rw [hmix]

theorem jumpKillLiftμ (i : B₂γ0.Inst ℓKAμ S2c) (q : MvPolynomial (Fin 2) ℚ) :
    B₂γ0.flatJump (s := S2c) i q = 0 := by
  unfold ColorModel.flatJump
  rw [rateKAμ, map_zero, zero_mul]

theorem jumpKillOuterμ (i : B₂γ0.Inst ℓKBμ S2c) (q : MvPolynomial (Fin 2) ℚ) :
    B₂γ0.flatJump (s := S2c) i q = 0 := by
  unfold ColorModel.flatJump
  rw [rateKBμ, map_zero, zero_mul]

/-- The tower's instance-jump sum: only the lifted inner death
contributes (there are no outer edges at γ = 0). -/
theorem jumpSumμ (q : MvPolynomial (Fin 2) ℚ) :
    (∑ ℓ, ∑ i : B₂γ0.Inst ℓ S2c, B₂γ0.flatJump i q)
      = B₂γ0.flatJump (ℓ := ℓAμ) (s := S2c) (iAμ 0 (singleEmb (0 : Fin 1))) q
        + (B₂γ0.flatJump (ℓ := ℓAμ) (s := S2c) (iAμ 1 (singleEmb (0 : Fin 2))) q
          + B₂γ0.flatJump (ℓ := ℓAμ) (s := S2c) (iAμ 1 (singleEmb (1 : Fin 2))) q) := by
  have hz : ∀ ℓ' ∈ (Finset.univ : Finset B₂γ0.LegIx), ℓ' ≠ ℓAμ →
      (∑ i : B₂γ0.Inst ℓ' S2c, B₂γ0.flatJump i q) = 0 := by
    intro ℓ' _ h
    exact match ℓ', h with
      | .inl (.inl x), _ => x.elim0
      | .inl (.inr (.inl ε)), h =>
          absurd (congrArg
            (fun z => (Sum.inl (Sum.inr (Sum.inl z)) : B₂γ0.LegIx))
            (Subsingleton.elim ε 0)) h
      | .inl (.inr (.inr u)), _ =>
          Finset.sum_eq_zero fun i _ => jumpKillLiftμ i q
      | .inr (.inl ε), _ => ε.elim0
      | .inr (.inr u), _ =>
          Finset.sum_eq_zero fun i _ => jumpKillOuterμ i q
  have hA : (∑ i : B₂γ0.Inst ℓAμ S2c, B₂γ0.flatJump i q)
      = B₂γ0.flatJump (ℓ := ℓAμ) (s := S2c) (iAμ 0 (singleEmb (0 : Fin 1))) q
        + (B₂γ0.flatJump (ℓ := ℓAμ) (s := S2c) (iAμ 1 (singleEmb (0 : Fin 2))) q
          + B₂γ0.flatJump (ℓ := ℓAμ) (s := S2c) (iAμ 1 (singleEmb (1 : Fin 2))) q) := by
    show (∑ i : (t : Fin 2) × (Fin 1 ↪ (S2cStrat t).T),
        B₂γ0.flatJump (ℓ := ℓAμ) (s := S2c) (iAμ i.1 i.2) q) = _
    exact sumA fun i => B₂γ0.flatJump (ℓ := ℓAμ) (s := S2c) (iAμ i.1 i.2) q
  exact (Finset.sum_eq_single_of_mem ℓAμ (Finset.mem_univ _) hz).trans hA

/-- The flattened-stratum death transfer: the engine at `muShape`. -/
theorem kerF (e : Fin 1 ↪ (ColorModel.muShape S2c).T) (c : B₁.legMix ℓF) :
    bind₁ (B₁.instKer (ℓ := ℓF) (s := ColorModel.muShape S2c) (iF e) c)
        (bind₁ (B₁.χ (B₁.instTgt (ℓ := ℓF) (s := ColorModel.muShape S2c)
          (iF e) c)) (X 1))
      = poolF - tokF (e 0) := by
  rw [bind₁_X_right]
  have hstep := CM₀.bind₁_jumpKer_poolC (ColorModel.muShape S2c) e
    (fun p : Fin 0 => death₁.bStrat c p)
    (fun p : Fin 0 => death₁.bKer (ColorModel.muShape S2c) e c p) (X 0)
  have h2 : (∑ r : Fin 1, CM₀.tokEmb (ColorModel.muShape S2c) (e r)
        (bind₁ (CM₀.χ ((ColorModel.muShape S2c).strat (e r))) (X 0)))
      = CM₀.tokEmb (ColorModel.muShape S2c) (e 0)
          (bind₁ (CM₀.χ ((ColorModel.muShape S2c).strat (e 0))) (X 0)) :=
    Fin.sum_univ_one _
  rw [Fin.sum_univ_zero, add_zero, h2, bind₁_X_right] at hstep
  exact hstep

/-- Flat jump of one flattened-stratum death instance. -/
theorem jumpF (e : Fin 1 ↪ (ColorModel.muShape S2c).T) :
    B₁.flatJump (ℓ := ℓF) (s := ColorModel.muShape S2c) (iF e) (X 1)
      = C 3 * ((poolF - tokF (e 0)) - poolF) := by
  unfold ColorModel.flatJump
  rw [rateF, bind₁_C_right, compile_poolF]
  have hmix : (∑ c, C (B₁.legW ℓF c)
        * bind₁ (B₁.instKer (ℓ := ℓF) (s := ColorModel.muShape S2c) (iF e) c)
            (bind₁ (B₁.χ (B₁.instTgt (ℓ := ℓF) (s := ColorModel.muShape S2c)
              (iF e) c)) (X 1)))
      = poolF - tokF (e 0) := by
    refine (Finset.sum_eq_single_of_mem cF (Finset.mem_univ _)
      (fun b _ hb => absurd
        (@Subsingleton.elim _ (inferInstanceAs (Subsingleton PUnit.{1})) b cF)
        hb)).trans ?_
    show C (B₁.legW ℓF cF)
        * bind₁ (B₁.instKer (ℓ := ℓF) (s := ColorModel.muShape S2c) (iF e) cF)
            (bind₁ (B₁.χ (B₁.instTgt (ℓ := ℓF) (s := ColorModel.muShape S2c)
              (iF e) cF)) (X 1))
      = poolF - tokF (e 0)
    rw [show B₁.legW ℓF cF = (1 : ℚ) from rfl, C_1, one_mul]
    exact kerF e cF
  rw [hmix]

theorem jumpKillF (i : B₁.Inst ℓKF (ColorModel.muShape S2c))
    (q : MvPolynomial (Fin 2) ℚ) :
    B₁.flatJump (s := ColorModel.muShape S2c) i q = 0 := by
  unfold ColorModel.flatJump
  rw [rateKF, map_zero, zero_mul]

/-- Enumerating a sum over the flattened token index (a sigma). -/
theorem sumμT {A : Type*} [AddCommMonoid A]
    (F : ((t : Fin 2) × (S2cStrat t).T) → A) :
    (∑ tk, F tk)
      = F ⟨0, (0 : Fin 1)⟩ + (F ⟨1, (0 : Fin 2)⟩ + F ⟨1, (1 : Fin 2)⟩) := by
  rw [sum_sigma_univ]
  calc (∑ t : Fin 2, ∑ k : (S2cStrat t).T, F ⟨t, k⟩)
      = (∑ k : (S2cStrat 0).T, F ⟨0, k⟩) + ∑ k : (S2cStrat 1).T, F ⟨1, k⟩ :=
        Fin.sum_univ_two _
    _ = (∑ k : Fin 1, F ⟨0, k⟩) + ∑ k : Fin 2, F ⟨1, k⟩ := rfl
    _ = F ⟨0, (0 : Fin 1)⟩ + (F ⟨1, (0 : Fin 2)⟩ + F ⟨1, (1 : Fin 2)⟩) := by
        rw [Fin.sum_univ_one, Fin.sum_univ_two]

/-- Enumerating a sum over flattened-token selections. -/
theorem sumF {A : Type*} [AddCommMonoid A]
    (F : (Fin 1 ↪ (ColorModel.muShape S2c).T) → A) :
    (∑ e, F e)
      = F (singleEmb ⟨0, (0 : Fin 1)⟩)
        + (F (singleEmb ⟨1, (0 : Fin 2)⟩) + F (singleEmb ⟨1, (1 : Fin 2)⟩)) := by
  rw [sum_emb_fin_one F]
  show (∑ tk : (t : Fin 2) × (S2cStrat t).T, F (singleEmb tk)) = _
  exact sumμT fun tk => F (singleEmb tk)

/-- The flattened stratum's instance-jump sum: one death instance per
flattened token. -/
theorem jumpSumF (q : MvPolynomial (Fin 2) ℚ) :
    (∑ ℓ, ∑ i : B₁.Inst ℓ (ColorModel.muShape S2c), B₁.flatJump i q)
      = B₁.flatJump (ℓ := ℓF) (s := ColorModel.muShape S2c)
          (iF (singleEmb ⟨0, (0 : Fin 1)⟩)) q
        + (B₁.flatJump (ℓ := ℓF) (s := ColorModel.muShape S2c)
            (iF (singleEmb ⟨1, (0 : Fin 2)⟩)) q
          + B₁.flatJump (ℓ := ℓF) (s := ColorModel.muShape S2c)
              (iF (singleEmb ⟨1, (1 : Fin 2)⟩)) q) := by
  have hz : ∀ ℓ' ∈ (Finset.univ : Finset B₁.LegIx), ℓ' ≠ ℓF →
      (∑ i : B₁.Inst ℓ' (ColorModel.muShape S2c), B₁.flatJump i q) = 0 := by
    intro ℓ' _ h
    exact match ℓ', h with
      | .inl x, _ => x.elim0
      | .inr (.inl ε), h =>
          absurd (congrArg
            (fun z => (Sum.inr (Sum.inl z) : B₁.LegIx))
            (Subsingleton.elim ε 0)) h
      | .inr (.inr u), _ =>
          Finset.sum_eq_zero fun i _ => jumpKillF i q
  have hA : (∑ i : B₁.Inst ℓF (ColorModel.muShape S2c), B₁.flatJump i q)
      = B₁.flatJump (ℓ := ℓF) (s := ColorModel.muShape S2c)
          (iF (singleEmb ⟨0, (0 : Fin 1)⟩)) q
        + (B₁.flatJump (ℓ := ℓF) (s := ColorModel.muShape S2c)
            (iF (singleEmb ⟨1, (0 : Fin 2)⟩)) q
          + B₁.flatJump (ℓ := ℓF) (s := ColorModel.muShape S2c)
              (iF (singleEmb ⟨1, (1 : Fin 2)⟩)) q) := by
    show (∑ e : Fin 1 ↪ (ColorModel.muShape S2c).T,
        B₁.flatJump (ℓ := ℓF) (s := ColorModel.muShape S2c) (iF e) q) = _
    exact sumF fun e => B₁.flatJump (ℓ := ℓF) (s := ColorModel.muShape S2c) (iF e) q
  exact (Finset.sum_eq_single_of_mem ℓF (Finset.mem_univ _) hz).trans hA

/-- Presentation drift of the pulled-back colour-sum at the tower. -/
theorem hdMu : B₂γ0.pDrift 1 = C (-2) * X 1 := by
  show ((dRep₁ 1).sum fun k a => C a * X k) = C (-2) * X 1
  rw [show dRep₁ 1 = Finsupp.single 1 (-2 : ℚ) from rfl,
    Finsupp.sum_single_index (by simp)]

/-- Presentation drift of the colour-sum feature of `B₁`. -/
theorem hdF : B₁.pDrift 1 = C (-2) * X 1 := by
  show ((dRep₁ 1).sum fun k a => C a * X k) = C (-2) * X 1
  rw [show dRep₁ 1 = Finsupp.single 1 (-2 : ℚ) from rfl,
    Finsupp.sum_single_index (by simp)]

/-- The tower's flat generator on the pulled-back colour-sum, in
closed atoms. -/
theorem muLHS : B₂γ0.flatGen S2c (X 1)
    = C (-2) * poolXμ
      + (C 3 * ((poolXμ - flatXμ 0 (0 : Fin 1)) - poolXμ)
        + (C 3 * ((poolXμ - flatXμ 1 (0 : Fin 2)) - poolXμ)
          + C 3 * ((poolXμ - flatXμ 1 (1 : Fin 2)) - poolXμ))) := by
  show contOp (B₂γ0.fDrift S2c) (B₂γ0.fGram S2c) (bind₁ (B₂γ0.χ S2c) (X 1))
      - B₂γ0.fKill S2c * bind₁ (B₂γ0.χ S2c) (X 1)
      + (∑ ℓ, ∑ i : B₂γ0.Inst ℓ S2c, B₂γ0.flatJump i (X 1))
    = _
  rw [contOp_compile (B₂γ0.fDrift S2c) (B₂γ0.fGram S2c) (B₂γ0.χ S2c)
      B₂γ0.pDrift B₂γ0.pGram (B₂γ0.hDrift S2c) (B₂γ0.hGram S2c) (X 1),
    contOp_X, hdMu, algHom_C_mul,
    show B₂γ0.fKill S2c = 0 from rfl, zero_mul, sub_zero,
    jumpSumμ,
    jumpAμ 0 (singleEmb (0 : Fin 1)), jumpAμ 1 (singleEmb (0 : Fin 2)),
    jumpAμ 1 (singleEmb (1 : Fin 2)),
    show singleEmb (0 : Fin 1) 0 = (0 : Fin 1) from rfl,
    show singleEmb (0 : Fin 2) 0 = (0 : Fin 2) from rfl,
    show singleEmb (1 : Fin 2) 0 = (1 : Fin 2) from rfl,
    compile_poolμ]

/-- The once-lifted flat generator at the flattened stratum, in closed
atoms. -/
theorem muRHS : B₁.flatGen (ColorModel.muShape S2c) (X 1)
    = C (-2) * poolF
      + (C 3 * ((poolF - tokF ⟨0, (0 : Fin 1)⟩) - poolF)
        + (C 3 * ((poolF - tokF ⟨1, (0 : Fin 2)⟩) - poolF)
          + C 3 * ((poolF - tokF ⟨1, (1 : Fin 2)⟩) - poolF))) := by
  show contOp (B₁.fDrift (ColorModel.muShape S2c))
      (B₁.fGram (ColorModel.muShape S2c))
      (bind₁ (B₁.χ (ColorModel.muShape S2c)) (X 1))
      - B₁.fKill (ColorModel.muShape S2c)
        * bind₁ (B₁.χ (ColorModel.muShape S2c)) (X 1)
      + (∑ ℓ, ∑ i : B₁.Inst ℓ (ColorModel.muShape S2c), B₁.flatJump i (X 1))
    = _
  rw [contOp_compile (B₁.fDrift (ColorModel.muShape S2c))
      (B₁.fGram (ColorModel.muShape S2c)) (B₁.χ (ColorModel.muShape S2c))
      B₁.pDrift B₁.pGram (B₁.hDrift (ColorModel.muShape S2c))
      (B₁.hGram (ColorModel.muShape S2c)) (X 1),
    contOp_X, hdF, algHom_C_mul,
    show B₁.fKill (ColorModel.muShape S2c) = 0 from rfl, zero_mul, sub_zero,
    jumpSumF,
    jumpF (singleEmb ⟨0, (0 : Fin 1)⟩), jumpF (singleEmb ⟨1, (0 : Fin 2)⟩),
    jumpF (singleEmb ⟨1, (1 : Fin 2)⟩),
    show singleEmb (⟨0, (0 : Fin 1)⟩ : (ColorModel.muShape S2c).T) 0
      = (⟨0, (0 : Fin 1)⟩ : (ColorModel.muShape S2c).T) from rfl,
    show singleEmb (⟨1, (0 : Fin 2)⟩ : (ColorModel.muShape S2c).T) 0
      = (⟨1, (0 : Fin 2)⟩ : (ColorModel.muShape S2c).T) from rfl,
    show singleEmb (⟨1, (1 : Fin 2)⟩ : (ColorModel.muShape S2c).T) 0
      = (⟨1, (1 : Fin 2)⟩ : (ColorModel.muShape S2c).T) from rfl,
    compile_poolF]

/-- The pool transport along `Equiv.sigmaAssoc` — `mu_compat_pool`
instantiated at the fixture (the one μ-compat lemma doing the
work it was built for). -/
theorem hrenPool :
    rename (Equiv.sigmaAssoc fun t k => CM₀.st ((S2c.strat t).strat k)) poolF
      = poolXμ :=
  (CM₀.mu_compat_pool Φ₁ (Fin 1) (fun _ => death₁) dRep₁ hdRep₁ GRep₁ hGRep₁
    S2c 1).symm

/-- A flattened token's OU coordinate, in flat-variable form. -/
theorem tokF_X (tk : (ColorModel.muShape S2c).T) :
    tokF tk = X (⟨tk, 0⟩ : CM₀.bagSt (ColorModel.muShape S2c)) := by
  show CM₀.tokEmb (ColorModel.muShape S2c) tk (X 0)
    = X (⟨tk, 0⟩ : CM₀.bagSt (ColorModel.muShape S2c))
  rw [ColorModel.tokEmb_apply, rename_X]

/-- A nested token's OU coordinate, in flat-variable form. -/
theorem flatX_X (t : Fin 2) (k : (S2cStrat t).T) :
    flatX t k = X (⟨t, ⟨k, 0⟩⟩ : B₂.st S2c) := by
  have hin : CM₀.tokEmb (S2cStrat t) k (X 0)
      = X (⟨k, 0⟩ : CM₀.bagSt (S2cStrat t)) := by
    rw [ColorModel.tokEmb_apply, rename_X]
  refine (congrArg (B₁.tokEmb S2c t) hin).trans ?_
  show rename (fun i => (⟨t, i⟩ : B₁.bagSt S2c))
      (X (⟨k, 0⟩ : CM₀.bagSt (S2cStrat t)))
    = X (⟨t, ⟨k, 0⟩⟩ : B₂.st S2c)
  rw [rename_X]

/-- The token transport along `Equiv.sigmaAssoc`: a flattened token's
OU coordinate is the corresponding nested flat coordinate. -/
theorem hrenTok (tk : (ColorModel.muShape S2c).T) :
    rename (Equiv.sigmaAssoc fun t k => CM₀.st ((S2c.strat t).strat k))
        (tokF tk)
      = flatXμ tk.1 tk.2 := by
  rw [tokF_X tk, rename_X,
    show flatXμ tk.1 tk.2 = X (⟨tk.1, ⟨tk.2, 0⟩⟩ : B₂γ0.st S2c)
      from flatX_X tk.1 tk.2]
  rfl

set_option maxHeartbeats 800000 in
/-- **The μ-coherence law at the fixture cell** (edge-free/group-blind
fragment; scope per the module header): on the μ*-pulled-back
colour-sum certificate, the twice-lifted flat generator equals the
once-lifted flat generator at the flattened stratum, transported along
`Equiv.sigmaAssoc` — the polynomial-stratum shadow of `BagMonad.bagMu`
(`double-cat`, cited not imported). Compile-compatibility in general
is `mu_compat_pool`; this is the generator face at mode (2; 1, 2). -/
theorem mu_coherence_cell :
    B₂γ0.flatGen S2c (X 1)
      = rename (Equiv.sigmaAssoc fun t k => CM₀.st ((S2c.strat t).strat k))
          (B₁.flatGen (ColorModel.muShape S2c) (X 1)) := by
  -- the rename node is inherently cross-spelled (the frozen statement
  -- glues the tower's flat state to the flattened one), so kabstract
  -- never touches it: the whole gluing is term-composed.
  have hA : rename (Equiv.sigmaAssoc fun t k => CM₀.st ((S2c.strat t).strat k))
      (C (-2) * poolF) = C (-2) * poolXμ :=
    (algHom_C_mul _ (-2) poolF).trans (congrArg (fun z => C (-2) * z) hrenPool)
  have hB : ∀ tk : (ColorModel.muShape S2c).T,
      rename (Equiv.sigmaAssoc fun t k => CM₀.st ((S2c.strat t).strat k))
          (C 3 * ((poolF - tokF tk) - poolF))
        = C 3 * ((poolXμ - flatXμ tk.1 tk.2) - poolXμ) := fun tk =>
    (algHom_C_mul _ 3 _).trans (congrArg (fun z => C 3 * z)
      ((map_sub _ _ _).trans (congrArg₂ (· - ·)
        ((map_sub _ _ _).trans (congrArg₂ (· - ·) hrenPool (hrenTok tk)))
        hrenPool)))
  refine muLHS.trans (Eq.trans ?_ (congrArg
    (rename (Equiv.sigmaAssoc fun t k => CM₀.st ((S2c.strat t).strat k)))
    muRHS.symm))
  exact ((map_add
      (rename (Equiv.sigmaAssoc fun t k => CM₀.st ((S2c.strat t).strat k)))
      _ _).trans
    (congrArg₂ (· + ·) hA
      ((map_add _ _ _).trans (congrArg₂ (· + ·) (hB ⟨0, (0 : Fin 1)⟩)
        ((map_add _ _ _).trans (congrArg₂ (· + ·) (hB ⟨1, (0 : Fin 2)⟩)
          (hB ⟨1, (1 : Fin 2)⟩))))))).symm

/-- The square instantiated at the γ = 0 pulled-back tower (the μ-law's
in-scope system): machine-checked at the cell. -/
theorem muTower_square :
    B₂γ0.flatGen S2c (X 1)
      = bind₁ (B₂γ0.χ S2c)
          (B₂γ0.contRead (X 1) - B₂γ0.pKill * X 1)
        + ∑ ℓ, ∑ i : B₂γ0.Inst ℓ S2c,
            bind₁ (Sum.elim (B₂γ0.instHval i) (B₂γ0.χ S2c))
              (B₂γ0.dtRead ℓ (X 1)) :=
  ColorModel.models_square B₂γ0 S2c (X 1)

end Fixture

end BagLift

end Qtsl
