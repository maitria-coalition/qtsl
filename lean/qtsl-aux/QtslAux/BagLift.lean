import QtslAux.SdeGeneratorPoly
import Mathlib.Data.Fintype.Perm

/-! # The polymorphic Bag-lift square

The full Bag lift: the fixed-count plate square generalized along the
three deltas located below. The fixed-count ancestor — a plate
coherence square with the same statement shape and proof skeleton —
was proved first, and this module generalizes it. The acceptance
statements were fixed by preregistration before this module's first
line.

**The object.** A **ColorModel** packages, for one level of a nested
SDCPN, the two faces the design keeps in register:

* a **presentation** over feature coordinates `κ` — drift, gram, kill,
  and jump legs in distinguished-tuple form (opaque hidden-slot types
  `legE`, kernel-style claimed feature effects) — the Mechanism-shaped
  interface;
* a **stratified flat side** — an opaque stratum index `Shape` (never
  enumerated: the laziness discipline), per-stratum flat state spaces,
  per-stratum compiles `χ`, flat field data, and per-leg instance
  families whose jumps may CROSS strata (a marking-space-indexed
  family, by design);
* **feature-level coherence fields** tying the two — the coherence
  demand is finite and static.

`models_square` is the square, stated once, model-polymorphically:
the flat generator applied to a compiled certificate IS the compiled
presentation-reading. `ColorModel.bag` builds the lifted model — the
Bag arm as a lift consuming an arbitrary Mechanism-shaped color
presentation — and its coherence fields are THEOREMS given the
input's; `bag_square` is then `models_square` of the lifted model.
Nesting is literally `(CM.bag …).bag …`: function composition, no new
theorem per depth.

**The three deltas, located**:

1. *count-changing edges* enter through `jumpShape` (consume an
   injective tuple of tokens, birth fresh ones — post-jump token types
   are subtype ⊕ `Fin b`, never a dependent update) together with the
   dictionary's constant feature: a death decrements the count pool
   because the constant feature leaves with the token — the
   SwitchEdge-self-loop reading, visible in `bagLegG`.
2. *arity ≥ 2* enters through embedding-indexed selection
   (`Fin a ↪ S.T`); the `∏ a_P!` multiplicity dictionary is the
   ordered/unordered bridge `sum_embeddings_factorial`.
3. *the edge-family-enriched color profile* is the `legE`-slotted leg
   vocabulary plus stratified instances — which is exactly what lets
   the OUTPUT re-enter as INPUT (closure of the interface under the
   lift); lifted legs concatenate distinguished paths
   (`legE' = legE ⊕ κ`).

**The kill reading (a design decision, folded in):** the Bag former's
kill reading is absorption/token-removal — the input's `pKill`
promotes to an arity-1 removal leg in the lift (kill at level n =
ordinary next at level n+1); the output model is conservative
(`pKill' = 0`). First-to-die pooling remains the PLATE former's
reading (the fixed-count square), not this lift's.

**Unified jump species** (one tagged alphabet at this stratum):
every jump — inner color jumps, kill promotion, bag deaths,
births, read arcs — is one shape: consume an injective a-tuple, birth
b tokens. Read arcs are consume+identical-rebirth (derivable, not a
separate species: pools cannot tell).

**Strictness**: every identity below is an equality; the closure
witnesses (`dRep`/`GRep`, the spec-dictionary closure rows) are
linear-representation data, not scope hypotheses at the target
stratum.

**Fences** (fixed at preregistration): guard/boundary rows ride the
companion plane, not the generator; immediate-transition cascade is
compiler work (the square is asserted for 𝒯_I = ∅); cross-token
drivers (common noise) are a deliberately-untaken extension — the
bag gram is block-diagonal by construction.

**Universes**: fixed concretely — feature coordinates, flat states,
token types in `Type`; stratum indices in `Type 1`. `BagShape Shape`
is again `Type 1`, so the lift closes without universe motion.
-/

open MvPolynomial

namespace Qtsl

namespace BagLift

/-! ## 0. Keystones

The substitution chain rule and its order-2 iterate, plus two
sum-shuffles and two rename helpers. -/

section Keystones

variable {R : Type*} [CommSemiring R]

/-- **The substitution chain rule** (Elliott's compose theorem at the
polynomial semantics): `∂ᵢ (p ∘ g) = ∑ⱼ (∂ⱼ p ∘ g) · ∂ᵢ gⱼ`. -/
theorem pderiv_bind₁ {σ τ : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq τ]
    (g : σ → MvPolynomial τ R) (p : MvPolynomial σ R) (i : τ) :
    pderiv i (bind₁ g p) = ∑ j, bind₁ g (pderiv j p) * pderiv i (g j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p k hp =>
      have hstep : ∀ j : σ, pderiv j (p * X k)
          = pderiv j p * X k + p * (if k = j then 1 else 0) := by
        intro j
        rw [pderiv_mul]
        by_cases h : k = j
        · subst h; simp
        · simp [pderiv_X_of_ne h, h]
      calc pderiv i (bind₁ g (p * X k))
          = pderiv i (bind₁ g p) * g k + bind₁ g p * pderiv i (g k) := by
            rw [map_mul, bind₁_X_right, pderiv_mul]
        _ = (∑ j, bind₁ g (pderiv j p) * pderiv i (g j)) * g k
              + bind₁ g p * pderiv i (g k) := by rw [hp]
        _ = (∑ j, bind₁ g (pderiv j p) * g k * pderiv i (g j))
              + ∑ j, (if k = j then bind₁ g p * pderiv i (g j) else 0) := by
            rw [Finset.sum_mul, Finset.sum_ite_eq (Finset.univ) k
              (fun j => bind₁ g p * pderiv i (g j))]
            simp only [Finset.mem_univ, if_true]
            congr 1
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ j, bind₁ g (pderiv j (p * X k)) * pderiv i (g j) := by
            rw [← Finset.sum_add_distrib]
            refine (Finset.sum_congr rfl fun j _ => ?_).symm
            rw [hstep j, map_add, map_mul, map_mul, bind₁_X_right]
            by_cases h : k = j
            · subst h; simp [add_mul]
            · simp [h]

/-- **The second-order substitution chain rule**: two applications of
`pderiv_bind₁` with the product rule in between. -/
theorem pderiv_pderiv_bind₁ {σ τ : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq τ]
    (g : σ → MvPolynomial τ R) (p : MvPolynomial σ R) (v v' : τ) :
    pderiv v (pderiv v' (bind₁ g p))
      = (∑ j, bind₁ g (pderiv j p) * pderiv v (pderiv v' (g j)))
        + ∑ j, ∑ l, bind₁ g (pderiv l (pderiv j p)) * pderiv v (g l) * pderiv v' (g j) := by
  rw [pderiv_bind₁ g p v', map_sum]
  have hterm : ∀ j : σ, pderiv v (bind₁ g (pderiv j p) * pderiv v' (g j))
      = bind₁ g (pderiv j p) * pderiv v (pderiv v' (g j))
        + (∑ l, bind₁ g (pderiv l (pderiv j p)) * pderiv v (g l)) * pderiv v' (g j) := by
    intro j
    rw [pderiv_mul, pderiv_bind₁ g (pderiv j p) v]
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]

/-- `pderiv` along a variable outside the image of a rename is zero. -/
theorem pderiv_rename_of_notMem {σ τ : Type*} [DecidableEq σ] [DecidableEq τ]
    {f : σ → τ} {y : τ} (hy : ∀ x, f x ≠ y) (p : MvPolynomial σ R) :
    pderiv y (rename f p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p a h =>
      rw [map_mul, rename_X, pderiv_mul, h, zero_mul, zero_add,
        pderiv_X_of_ne (hy a), mul_zero]

/-- Substituting variables-for-variables is a rename. -/
theorem bind₁_X_comp {σ τ : Type*} (h : σ → τ) :
    (bind₁ fun i => (X (h i) : MvPolynomial τ R)) = rename h :=
  MvPolynomial.algHom_ext fun i => by simp

/-- The identity substitution, pointwise. -/
theorem bind₁_X_self {σ : Type*} (p : MvPolynomial σ R) :
    bind₁ (X : σ → MvPolynomial σ R) p = p := by
  rw [bind₁_X_left]
  rfl

/-- Substituting a `Sum.elim` against a right-injection rename reads
the right branch. -/
theorem bind₁_elim_inr {α β γ : Type*} (f : α → MvPolynomial γ R)
    (g : β → MvPolynomial γ R) (p : MvPolynomial β R) :
    bind₁ (Sum.elim f g) (rename Sum.inr p) = bind₁ g p := by
  rw [bind₁_rename]
  rfl

/-- Substituting a `Sum.elim` against a left-injection rename reads
the left branch. -/
theorem bind₁_elim_inl {α β γ : Type*} (f : α → MvPolynomial γ R)
    (g : β → MvPolynomial γ R) (p : MvPolynomial α R) :
    bind₁ (Sum.elim f g) (rename Sum.inl p) = bind₁ f p := by
  rw [bind₁_rename]
  rfl

/-- Algebra homomorphisms of polynomial rings pull constants out of
products. -/
theorem algHom_C_mul {σ τ : Type*} {S : Type*} [CommSemiring S]
    (A : MvPolynomial σ S →ₐ[S] MvPolynomial τ S)
    (a : S) (x : MvPolynomial σ S) : A (C a * x) = C a * A x := by
  rw [← algebraMap_eq, map_mul, AlgHom.commutes, algebraMap_eq]

/-- Pull the third index of a triple sum to the front. -/
theorem sum_swap_3 {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [AddCommMonoid M] (f : α → β → γ → M) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc (∑ a, ∑ b, ∑ c, f a b c)
      = ∑ a, ∑ c, ∑ b, f a b c := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm

/-- Pull the third and fourth indices of a quadruple sum to the front. -/
theorem sum_swap_4 {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] [AddCommMonoid M] (f : α → β → γ → δ → M) :
    (∑ a, ∑ b, ∑ c, ∑ e, f a b c e) = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e := by
  calc (∑ a, ∑ b, ∑ c, ∑ e, f a b c e)
      = ∑ a, ∑ c, ∑ e, ∑ b, f a b c e := by
        refine Finset.sum_congr rfl fun a _ => ?_
        calc (∑ b, ∑ c, ∑ e, f a b c e)
            = ∑ c, ∑ b, ∑ e, f a b c e := Finset.sum_comm
          _ = ∑ c, ∑ e, ∑ b, f a b c e := by
              refine Finset.sum_congr rfl fun c _ => ?_
              exact Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ e, ∑ b, f a b c e := Finset.sum_comm
    _ = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e := by
        refine Finset.sum_congr rfl fun c _ => ?_
        exact Finset.sum_comm

end Keystones

/-! ## 1. The two graded operators, defined once for both faces

`contOp` (drift + ½·Hessian-against-gram) and `gramOp` (the carré du
champ in gram-contraction form) are defined over an arbitrary finite
variable type, so that ONE definition serves the flat side (variables
= a stratum's state coordinates) and the presentation side (variables
= feature coordinates): `contRead`/`gramRead` below are these same
operators at the feature level. `contOp_compile`/`gramOp_compile` are
the chain-rule collection lemmas: feature-level coherence at single
features propagates to ALL certificates — the finite-and-static
coherence demand, as a theorem. -/

section Ops

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Drift + half-Hessian-against-gram: the continuous (order ≤ 2)
generator families applied to an observable. -/
noncomputable def contOp (f : V → MvPolynomial V ℚ)
    (G : V → V → MvPolynomial V ℚ) (W : MvPolynomial V ℚ) :
    MvPolynomial V ℚ :=
  (∑ v, f v * pderiv v W)
    + C (1/2 : ℚ) * ∑ v, ∑ v', G v v' * pderiv v (pderiv v' W)

/-- The carré du champ in gram-contraction form. -/
noncomputable def gramOp (G : V → V → MvPolynomial V ℚ)
    (W W' : MvPolynomial V ℚ) : MvPolynomial V ℚ :=
  ∑ v, ∑ v', G v v' * pderiv v W * pderiv v' W'

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The chain-rule expansion of `contOp` on a substituted polynomial:
first-derivative terms pair with `contOp` of the assignments,
second-derivative terms with their `gramOp`. -/
theorem contOp_bind₁ (f : V → MvPolynomial V ℚ)
    (G : V → V → MvPolynomial V ℚ) (g : κ → MvPolynomial V ℚ)
    (q : MvPolynomial κ ℚ) :
    contOp f G (bind₁ g q)
      = (∑ j, bind₁ g (pderiv j q) * contOp f G (g j))
        + C (1/2 : ℚ) * ∑ j, ∑ l,
            bind₁ g (pderiv l (pderiv j q)) * gramOp G (g l) (g j) := by
  have hdrift : (∑ v, f v * pderiv v (bind₁ g q))
      = ∑ j, bind₁ g (pderiv j q) * ∑ v, f v * pderiv v (g j) := by
    calc (∑ v, f v * pderiv v (bind₁ g q))
        = ∑ v, ∑ j, bind₁ g (pderiv j q) * (f v * pderiv v (g j)) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [pderiv_bind₁, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, ∑ v, bind₁ g (pderiv j q) * (f v * pderiv v (g j)) :=
          Finset.sum_comm
      _ = ∑ j, bind₁ g (pderiv j q) * ∑ v, f v * pderiv v (g j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
  have hhess : (∑ v, ∑ v', G v v' * pderiv v (pderiv v' (bind₁ g q)))
      = (∑ j, bind₁ g (pderiv j q)
            * ∑ v, ∑ v', G v v' * pderiv v (pderiv v' (g j)))
        + ∑ j, ∑ l, bind₁ g (pderiv l (pderiv j q)) * gramOp G (g l) (g j) := by
    have hexpand : (∑ v, ∑ v', G v v' * pderiv v (pderiv v' (bind₁ g q)))
        = ∑ v, ∑ v',
            ((∑ j, bind₁ g (pderiv j q) * (G v v' * pderiv v (pderiv v' (g j))))
              + ∑ j, ∑ l, bind₁ g (pderiv l (pderiv j q))
                  * (G v v' * pderiv v (g l) * pderiv v' (g j))) := by
      refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun v' _ => ?_
      rw [pderiv_pderiv_bind₁, mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by ring
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
    rw [hexpand]
    have hsplit : ∀ v : V,
        (∑ v', ((∑ j, bind₁ g (pderiv j q) * (G v v' * pderiv v (pderiv v' (g j))))
            + ∑ j, ∑ l, bind₁ g (pderiv l (pderiv j q))
                * (G v v' * pderiv v (g l) * pderiv v' (g j))))
          = (∑ v', ∑ j, bind₁ g (pderiv j q) * (G v v' * pderiv v (pderiv v' (g j))))
            + ∑ v', ∑ j, ∑ l, bind₁ g (pderiv l (pderiv j q))
                * (G v v' * pderiv v (g l) * pderiv v' (g j)) :=
      fun v => Finset.sum_add_distrib
    rw [Finset.sum_congr rfl fun v (_ : v ∈ Finset.univ) => hsplit v,
      Finset.sum_add_distrib]
    congr 1
    · rw [sum_swap_3 fun v v' j =>
        bind₁ g (pderiv j q) * (G v v' * pderiv v (pderiv v' (g j)))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.mul_sum]
    · rw [sum_swap_4 fun v v' j l => bind₁ g (pderiv l (pderiv j q))
        * (G v v' * pderiv v (g l) * pderiv v' (g j))]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      unfold gramOp
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.mul_sum]
  unfold contOp
  rw [hdrift, hhess, mul_add, Finset.mul_sum]
  have hhalf : (∑ j, C (1/2 : ℚ) * (bind₁ g (pderiv j q)
        * ∑ v, ∑ v', G v v' * pderiv v (pderiv v' (g j))))
      = ∑ j, bind₁ g (pderiv j q)
          * (C (1/2 : ℚ) * ∑ v, ∑ v', G v v' * pderiv v (pderiv v' (g j))) :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [hhalf, ← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Feature-level coherence propagates to all certificates**
(continuous face): if `contOp` on each assignment and `gramOp` on each
assignment pair are the compiled presentation fields, then `contOp` on
ANY compiled certificate is the compiled presentation-level `contOp`.
Note the presentation side reuses the SAME operator at feature
coordinates. -/
theorem contOp_compile (f : V → MvPolynomial V ℚ)
    (G : V → V → MvPolynomial V ℚ) (g : κ → MvPolynomial V ℚ)
    (pd : κ → MvPolynomial κ ℚ) (pG : κ → κ → MvPolynomial κ ℚ)
    (hd : ∀ j, contOp f G (g j) = bind₁ g (pd j))
    (hG : ∀ j l, gramOp G (g j) (g l) = bind₁ g (pG j l))
    (q : MvPolynomial κ ℚ) :
    contOp f G (bind₁ g q) = bind₁ g (contOp pd pG q) := by
  have h1 : bind₁ g (∑ j, pd j * pderiv j q)
      = ∑ j, bind₁ g (pd j) * bind₁ g (pderiv j q) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_mul _ _ _
  have h2 : bind₁ g (∑ j, ∑ l, pG j l * pderiv j (pderiv l q))
      = ∑ j, ∑ l, bind₁ g (pG j l) * bind₁ g (pderiv j (pderiv l q)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun l _ => map_mul _ _ _
  have hrhs : bind₁ g (contOp pd pG q)
      = (∑ j, bind₁ g (pd j) * bind₁ g (pderiv j q))
        + C (1/2 : ℚ) * ∑ j, ∑ l,
            bind₁ g (pG j l) * bind₁ g (pderiv j (pderiv l q)) := by
    unfold contOp
    rw [map_add, algHom_C_mul, h1, h2]
  have hA : (∑ j, bind₁ g (pderiv j q) * contOp f G (g j))
      = ∑ j, bind₁ g (pd j) * bind₁ g (pderiv j q) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hd j, mul_comm]
  have hB : (∑ j, ∑ l, bind₁ g (pderiv l (pderiv j q)) * gramOp G (g l) (g j))
      = ∑ j, ∑ l, bind₁ g (pG j l) * bind₁ g (pderiv j (pderiv l q)) :=
    calc (∑ j, ∑ l, bind₁ g (pderiv l (pderiv j q)) * gramOp G (g l) (g j))
        = ∑ j, ∑ l, bind₁ g (pderiv l (pderiv j q)) * bind₁ g (pG l j) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
          rw [hG l j]
      _ = ∑ l, ∑ j, bind₁ g (pderiv l (pderiv j q)) * bind₁ g (pG l j) :=
          Finset.sum_comm
      _ = ∑ j, ∑ l, bind₁ g (pG j l) * bind₁ g (pderiv j (pderiv l q)) := by
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
          rw [mul_comm]
  rw [contOp_bind₁, hrhs, hA, hB]

/-- Feature-level coherence propagates to all certificates (carré
face). -/
theorem gramOp_compile (G : V → V → MvPolynomial V ℚ)
    (g : κ → MvPolynomial V ℚ) (pG : κ → κ → MvPolynomial κ ℚ)
    (hG : ∀ j l, gramOp G (g j) (g l) = bind₁ g (pG j l))
    (ψ φ : MvPolynomial κ ℚ) :
    gramOp G (bind₁ g ψ) (bind₁ g φ) = bind₁ g (gramOp pG ψ φ) := by
  calc gramOp G (bind₁ g ψ) (bind₁ g φ)
      = ∑ v, ∑ v', ∑ l, ∑ j, bind₁ g (pderiv j ψ) * bind₁ g (pderiv l φ)
          * (G v v' * pderiv v (g j) * pderiv v' (g l)) := by
        unfold gramOp
        refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun v' _ => ?_
        rw [pderiv_bind₁ g ψ v, pderiv_bind₁ g φ v', Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ l, ∑ j, ∑ v, ∑ v', bind₁ g (pderiv j ψ) * bind₁ g (pderiv l φ)
          * (G v v' * pderiv v (g j) * pderiv v' (g l)) :=
        sum_swap_4 fun v v' l j => bind₁ g (pderiv j ψ) * bind₁ g (pderiv l φ)
          * (G v v' * pderiv v (g j) * pderiv v' (g l))
    _ = ∑ l, ∑ j, bind₁ g (pG j l * pderiv j ψ * pderiv l φ) := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, map_mul, ← hG j l]
        unfold gramOp
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun v' _ => ?_
        ring
    _ = ∑ j, ∑ l, bind₁ g (pG j l * pderiv j ψ * pderiv l φ) :=
        Finset.sum_comm
    _ = bind₁ g (∑ j, ∑ l, pG j l * pderiv j ψ * pderiv l φ) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => (map_sum _ _ _).symm
    _ = bind₁ g (gramOp pG ψ φ) := by
        unfold gramOp
        rfl

/-- `contOp` on a coordinate reads the drift field. -/
theorem contOp_X (f : V → MvPolynomial V ℚ) (G : V → V → MvPolynomial V ℚ)
    (j : V) : contOp f G (X j) = f j := by
  unfold contOp
  have h1 : (∑ v, f v * pderiv v (X j : MvPolynomial V ℚ)) = f j := by
    rw [Finset.sum_eq_single j]
    · rw [pderiv_X_self, mul_one]
    · intro v _ hv
      rw [pderiv_X_of_ne (Ne.symm hv), mul_zero]
    · exact fun h => absurd (Finset.mem_univ j) h
  have h2 : (∑ v, ∑ v', G v v'
      * pderiv v (pderiv v' (X j : MvPolynomial V ℚ))) = 0 := by
    refine Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun v' _ => ?_
    by_cases h : v' = j
    · subst h
      simp
    · rw [pderiv_X_of_ne (Ne.symm h), map_zero, mul_zero]
  rw [h1, h2, mul_zero, add_zero]

/-- `gramOp` on a coordinate pair reads the gram field. -/
theorem gramOp_X (G : V → V → MvPolynomial V ℚ) (j l : V) :
    gramOp G (X j) (X l) = G j l := by
  unfold gramOp
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single l]
    · rw [pderiv_X_self, pderiv_X_self, mul_one, mul_one]
    · intro v' _ hv'
      rw [pderiv_X_of_ne (Ne.symm hv'), mul_zero]
    · exact fun h => absurd (Finset.mem_univ l) h
  · intro v _ hv
    refine Finset.sum_eq_zero fun v' _ => ?_
    rw [pderiv_X_of_ne (Ne.symm hv), mul_zero, zero_mul]
  · exact fun h => absurd (Finset.mem_univ j) h

/-- `contOp` kills constants. -/
theorem contOp_C (f : V → MvPolynomial V ℚ) (G : V → V → MvPolynomial V ℚ)
    (c : ℚ) : contOp f G (C c) = 0 := by
  unfold contOp
  simp

/-- `contOp` kills `1`. -/
theorem contOp_one (f : V → MvPolynomial V ℚ) (G : V → V → MvPolynomial V ℚ) :
    contOp f G (1 : MvPolynomial V ℚ) = 0 := by
  rw [← C_1, contOp_C]

/-- `gramOp` kills a constant slot (left). -/
theorem gramOp_C_left (G : V → V → MvPolynomial V ℚ) (c : ℚ)
    (ψ : MvPolynomial V ℚ) : gramOp G (C c) ψ = 0 := by
  unfold gramOp
  simp

/-- `gramOp` kills a constant slot (right). -/
theorem gramOp_C_right (G : V → V → MvPolynomial V ℚ) (c : ℚ)
    (ψ : MvPolynomial V ℚ) : gramOp G ψ (C c) = 0 := by
  unfold gramOp
  simp

/-- `gramOp` kills `1` (left). -/
theorem gramOp_one_left (G : V → V → MvPolynomial V ℚ)
    (ψ : MvPolynomial V ℚ) : gramOp G (1 : MvPolynomial V ℚ) ψ = 0 := by
  rw [← C_1, gramOp_C_left]

/-- `gramOp` kills `1` (right). -/
theorem gramOp_one_right (G : V → V → MvPolynomial V ℚ)
    (ψ : MvPolynomial V ℚ) : gramOp G ψ (1 : MvPolynomial V ℚ) = 0 := by
  rw [← C_1, gramOp_C_right]

end Ops

/-! ## 2. The interface: `ColorModel`

The recursion carrier: a Courrège-graded presentation over
feature coordinates + a stratified flat instantiation + feature-level
coherence. `Shape` is opaque and only ever ∀-quantified — the formal
content of "never materialize the mode vocabulary". -/

/-- One level of a nested SDCPN, both faces in register. See the
module docstring; field groups: presentation (`p*`, `leg*`), flat
(`st`, `χ`, `f*`), instances (`Inst`, `inst*`), coherence (`h*`). -/
structure ColorModel (Shape : Type 1) (κ : Type) [Fintype κ] [DecidableEq κ] :
    Type 1 where
  /-- per-stratum flat state coordinates -/
  st : Shape → Type
  [instStF : ∀ s, Fintype (st s)]
  [instStD : ∀ s, DecidableEq (st s)]
  /-- per-stratum compile of features into flat observables -/
  χ : (s : Shape) → κ → MvPolynomial (st s) ℚ
  /-- presentation drift: the claimed local generator on each feature -/
  pDrift : κ → MvPolynomial κ ℚ
  /-- presentation gram: the claimed carré du champ on feature pairs -/
  pGram : κ → κ → MvPolynomial κ ℚ
  /-- presentation killing rate (order-0 family) -/
  pKill : MvPolynomial κ ℚ
  /-- jump-leg index -/
  LegIx : Type
  [instLegIxF : Fintype LegIx]
  /-- hidden distinguished-path slots, per leg (opaque) -/
  legE : LegIx → Type
  [instLegEF : ∀ ℓ, Fintype (legE ℓ)]
  [instLegED : ∀ ℓ, DecidableEq (legE ℓ)]
  /-- leg rate over (hidden slots ⊕ features) -/
  legRate : (ℓ : LegIx) → MvPolynomial (legE ℓ ⊕ κ) ℚ
  /-- mixture-component index, per leg -/
  legMix : LegIx → Type
  [instLegMixF : ∀ ℓ, Fintype (legMix ℓ)]
  /-- mixture weights -/
  legW : (ℓ : LegIx) → legMix ℓ → ℚ
  /-- claimed post-jump features, kernel-style, per component -/
  legG : (ℓ : LegIx) → legMix ℓ → κ → MvPolynomial (legE ℓ ⊕ κ) ℚ
  /-- flat drift, per stratum -/
  fDrift : (s : Shape) → st s → MvPolynomial (st s) ℚ
  /-- flat gram, per stratum -/
  fGram : (s : Shape) → st s → st s → MvPolynomial (st s) ℚ
  /-- flat killing rate, per stratum -/
  fKill : (s : Shape) → MvPolynomial (st s) ℚ
  /-- flat instance family of each leg at each stratum -/
  Inst : LegIx → Shape → Type
  [instInstF : ∀ ℓ s, Fintype (Inst ℓ s)]
  /-- hidden values of an instance (the distinguished path's flat
  reading) -/
  instHval : {ℓ : LegIx} → {s : Shape} → Inst ℓ s → legE ℓ →
    MvPolynomial (st s) ℚ
  /-- target stratum of an instance's mixture component (jumps may
  cross strata: the T-DESC family) -/
  instTgt : {ℓ : LegIx} → {s : Shape} → Inst ℓ s → legMix ℓ → Shape
  /-- flat transfer kernel of an instance's component: assigns to each
  target-stratum coordinate a pre-jump observable -/
  instKer : {ℓ : LegIx} → {s : Shape} → (i : Inst ℓ s) → (c : legMix ℓ) →
    st (instTgt i c) → MvPolynomial (st s) ℚ
  /-- coherence: the flat local generator on each compiled feature is
  the compiled presentation drift -/
  hDrift : ∀ (s : Shape) (j : κ),
    contOp (fDrift s) (fGram s) (χ s j) = bind₁ (χ s) (pDrift j)
  /-- coherence: the flat carré on compiled feature pairs is the
  compiled presentation gram -/
  hGram : ∀ (s : Shape) (j l : κ),
    gramOp (fGram s) (χ s j) (χ s l) = bind₁ (χ s) (pGram j l)
  /-- coherence: flat kill is compiled presentation kill -/
  hKill : ∀ s : Shape, fKill s = bind₁ (χ s) pKill
  /-- coherence: each flat kernel's feature effect is the claimed one,
  read at (hidden values ⊕ compiled features) -/
  hKer : ∀ {ℓ : LegIx} {s : Shape} (i : Inst ℓ s) (c : legMix ℓ) (j : κ),
    bind₁ (instKer i c) (χ (instTgt i c) j)
      = bind₁ (Sum.elim (instHval i) (χ s)) (legG ℓ c j)

attribute [instance] ColorModel.instStF ColorModel.instStD
  ColorModel.instLegIxF ColorModel.instLegEF ColorModel.instLegED
  ColorModel.instLegMixF ColorModel.instInstF

namespace ColorModel

variable {Shape : Type 1} {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The presentation-level continuous reading: `contOp` at feature
coordinates. -/
noncomputable def contRead (M : ColorModel Shape κ) :
    MvPolynomial κ ℚ → MvPolynomial κ ℚ :=
  contOp M.pDrift M.pGram

/-- The presentation-level carré reading: `gramOp` at feature
coordinates. -/
noncomputable def gramRead (M : ColorModel Shape κ) :
    MvPolynomial κ ℚ → MvPolynomial κ ℚ → MvPolynomial κ ℚ :=
  gramOp M.pGram

/-- The presentation reading of a coordinate is its drift field. -/
theorem contRead_X (M : ColorModel Shape κ) (j : κ) :
    M.contRead (X j) = M.pDrift j :=
  contOp_X M.pDrift M.pGram j

/-- The presentation carré of a coordinate pair is its gram field. -/
theorem gramRead_X (M : ColorModel Shape κ) (j l : κ) :
    M.gramRead (X j) (X l) = M.pGram j l :=
  gramOp_X M.pGram j l

/-- The distinguished-path jump reading of a certificate under one
leg: rate times (mixture-shifted certificate minus certificate), over
(hidden slots ⊕ features) — `Ldt`'s shape, leg-generic. -/
noncomputable def dtRead (M : ColorModel Shape κ) (ℓ : M.LegIx)
    (q : MvPolynomial κ ℚ) : MvPolynomial (M.legE ℓ ⊕ κ) ℚ :=
  M.legRate ℓ
    * ((∑ c, C (M.legW ℓ c) * bind₁ (M.legG ℓ c) q) - rename Sum.inr q)

/-- Kernel coherence propagates from features to all certificates
(the jump-face sibling of `contOp_compile`). -/
theorem instKer_compile (M : ColorModel Shape κ) {ℓ : M.LegIx} {s : Shape}
    (i : M.Inst ℓ s) (c : M.legMix ℓ) (ψ : MvPolynomial κ ℚ) :
    bind₁ (M.instKer i c) (bind₁ (M.χ (M.instTgt i c)) ψ)
      = bind₁ (Sum.elim (M.instHval i) (M.χ s)) (bind₁ (M.legG ℓ c) ψ) := by
  rw [bind₁_bind₁, bind₁_bind₁]
  have hfun : (fun j => bind₁ (M.instKer i c) (M.χ (M.instTgt i c) j))
      = fun j => bind₁ (Sum.elim (M.instHval i) (M.χ s)) (M.legG ℓ c j) :=
    funext fun j => M.hKer i c j
  rw [hfun]

/-- The flat jump term of one instance on a compiled certificate: the
rate (hidden values ⊕ compile of the leg rate) times (mixture of
cross-stratum transfers minus identity). -/
noncomputable def flatJump (M : ColorModel Shape κ) {ℓ : M.LegIx} {s : Shape}
    (i : M.Inst ℓ s) (q : MvPolynomial κ ℚ) : MvPolynomial (M.st s) ℚ :=
  bind₁ (Sum.elim (M.instHval i) (M.χ s)) (M.legRate ℓ)
    * ((∑ c, C (M.legW ℓ c)
          * bind₁ (M.instKer i c) (bind₁ (M.χ (M.instTgt i c)) q))
        - bind₁ (M.χ s) q)

/-- The full flat generator at stratum `s` applied to a compiled
certificate: continuous families + killing + all instance jumps. -/
noncomputable def flatGen (M : ColorModel Shape κ) (s : Shape)
    (q : MvPolynomial κ ℚ) : MvPolynomial (M.st s) ℚ :=
  contOp (M.fDrift s) (M.fGram s) (bind₁ (M.χ s) q)
    - M.fKill s * bind₁ (M.χ s) q
    + ∑ ℓ, ∑ i : M.Inst ℓ s, M.flatJump i q

/-- **THE SQUARE, model-polymorphically**: the flat generator of any
`ColorModel` on a compiled certificate IS the compile of the
presentation reading — continuous + killing faces through the
per-stratum compile, jump faces through the distinguished-path
dictionaries (hidden values ⊕ compile). `bag_square` below is this
theorem at a lifted model. -/
theorem models_square (M : ColorModel Shape κ) (s : Shape)
    (q : MvPolynomial κ ℚ) :
    M.flatGen s q
      = bind₁ (M.χ s) (M.contRead q - M.pKill * q)
        + ∑ ℓ, ∑ i : M.Inst ℓ s,
            bind₁ (Sum.elim (M.instHval i) (M.χ s)) (M.dtRead ℓ q) := by
  unfold flatGen
  have hcont : contOp (M.fDrift s) (M.fGram s) (bind₁ (M.χ s) q)
      = bind₁ (M.χ s) (M.contRead q) :=
    contOp_compile (M.fDrift s) (M.fGram s) (M.χ s) M.pDrift M.pGram
      (M.hDrift s) (M.hGram s) q
  have hkill : M.fKill s * bind₁ (M.χ s) q = bind₁ (M.χ s) (M.pKill * q) := by
    rw [M.hKill s, map_mul]
  have hjump : ∀ (ℓ : M.LegIx) (i : M.Inst ℓ s),
      M.flatJump i q
        = bind₁ (Sum.elim (M.instHval i) (M.χ s)) (M.dtRead ℓ q) := by
    intro ℓ i
    unfold flatJump dtRead
    rw [map_mul]
    congr 1
    rw [map_sub, map_sum]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_mul, algHom_C, algebraMap_eq, M.instKer_compile i c q]
    · rw [bind₁_elim_inr]
  rw [hcont, hkill, map_sub]
  congr 1
  exact Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun i _ => hjump ℓ i

end ColorModel

/-! ## 3. The atomic model, and the anchor to the computed generator

An atomic Mechanism (one stratum, features = coordinates, K1 legs) is
a `ColorModel`, and its flat generator IS
`Qtsl.SdeGeneratorPoly.genPoly` as already defined — the square is
about the computed generator, not a private redefinition. The atomic
arm is the identity leg of the recursion (the Mechanism arm IS the
dispatch). -/

section Atomic

open SdeGeneratorPoly

variable {n m : ℕ}

/-- The atomic `ColorModel` of a polynomial SDE-profile presentation:
one stratum, compile = identity, presentation fields read off the
profile, each K1 leg an arity-0-hidden same-stratum leg. (Reducible so
that its projections unfold during instance resolution and rewriting —
the anchor and fixtures match against raw `Fin n` vocabulary.) -/
@[reducible] noncomputable def ColorModel.atomic (P : PolyProfile n m) :
    ColorModel PUnit.{2} (Fin n) where
  st _ := Fin n
  χ _ := X
  pDrift j := P.f j
  pGram j l := P.gram j l
  pKill := P.kill
  LegIx := Fin P.legs.length
  legE _ := Fin 0
  legRate ℓ := rename Sum.inr (P.legs.get ℓ).1
  legMix ℓ := Fin (P.legs.get ℓ).2.length
  legW ℓ c := ((P.legs.get ℓ).2.get c).1
  legG ℓ c j := rename Sum.inr (((P.legs.get ℓ).2.get c).2 j)
  fDrift _ := P.f
  fGram _ := P.gram
  fKill _ := P.kill
  Inst _ _ := PUnit
  instHval _ x := x.elim0
  instTgt _ _ := PUnit.unit
  instKer := fun {ℓ} {_s} _i c => ((P.legs.get ℓ).2.get c).2
  hDrift _ j := by
    unfold contOp
    have h1 : (∑ v, P.f v * pderiv v (X j : MvPolynomial (Fin n) ℚ)) = P.f j := by
      rw [Finset.sum_eq_single j]
      · rw [pderiv_X_self, mul_one]
      · intro v _ hv
        rw [pderiv_X_of_ne (Ne.symm hv), mul_zero]
      · exact fun h => absurd (Finset.mem_univ j) h
    have h2 : (∑ v, ∑ v', P.gram v v'
        * pderiv v (pderiv v' (X j : MvPolynomial (Fin n) ℚ))) = 0 := by
      refine Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun v' _ => ?_
      by_cases h : v' = j
      · subst h
        simp
      · rw [pderiv_X_of_ne (Ne.symm h), map_zero, mul_zero]
    rw [h1, h2, mul_zero, add_zero, bind₁_X_self]
  hGram _ j l := by
    unfold gramOp
    have h1 : (∑ v, ∑ v', P.gram v v'
        * pderiv v (X j : MvPolynomial (Fin n) ℚ) * pderiv v' (X l)) = P.gram j l := by
      rw [Finset.sum_eq_single j]
      · rw [Finset.sum_eq_single l]
        · rw [pderiv_X_self, pderiv_X_self, mul_one, mul_one]
        · intro v' _ hv'
          rw [pderiv_X_of_ne (Ne.symm hv'), mul_zero]
        · exact fun h => absurd (Finset.mem_univ l) h
      · intro v _ hv
        refine Finset.sum_eq_zero fun v' _ => ?_
        rw [pderiv_X_of_ne (Ne.symm hv), mul_zero, zero_mul]
      · exact fun h => absurd (Finset.mem_univ j) h
    rw [h1, bind₁_X_self]
  hKill _ := (bind₁_X_self P.kill).symm
  hKer i c j := by
    rw [bind₁_rename]
    have helim : (Sum.elim (fun x : Fin 0 => x.elim0)
        (X : Fin n → MvPolynomial (Fin n) ℚ) ∘ Sum.inr) = X := rfl
    rw [helim, bind₁_X_self, bind₁_X_right]

@[simp] theorem atomic_st (P : PolyProfile n m) (s : PUnit.{2}) :
    (ColorModel.atomic P).st s = Fin n := rfl

@[simp] theorem atomic_χ (P : PolyProfile n m) (s : PUnit.{2}) :
    (ColorModel.atomic P).χ s = X := rfl

@[simp] theorem atomic_fDrift (P : PolyProfile n m) (s : PUnit.{2}) :
    (ColorModel.atomic P).fDrift s = P.f := rfl

@[simp] theorem atomic_fGram (P : PolyProfile n m) (s : PUnit.{2}) :
    (ColorModel.atomic P).fGram s = P.gram := rfl

@[simp] theorem atomic_fKill (P : PolyProfile n m) (s : PUnit.{2}) :
    (ColorModel.atomic P).fKill s = P.kill := rfl

@[simp] theorem atomic_legRate (P : PolyProfile n m)
    (ℓ : (ColorModel.atomic P).LegIx) :
    (ColorModel.atomic P).legRate ℓ = rename Sum.inr (P.legs.get ℓ).1 := rfl

@[simp] theorem atomic_legW (P : PolyProfile n m)
    (ℓ : (ColorModel.atomic P).LegIx) (c : (ColorModel.atomic P).legMix ℓ) :
    (ColorModel.atomic P).legW ℓ c = ((P.legs.get ℓ).2.get c).1 := rfl

@[simp] theorem atomic_instKer (P : PolyProfile n m)
    {ℓ : (ColorModel.atomic P).LegIx} {s : PUnit.{2}}
    (i : (ColorModel.atomic P).Inst ℓ s) (c : (ColorModel.atomic P).legMix ℓ) :
    (ColorModel.atomic P).instKer i c = ((P.legs.get ℓ).2.get c).2 := rfl

@[simp] theorem atomic_instHval (P : PolyProfile n m)
    {ℓ : (ColorModel.atomic P).LegIx} {s : PUnit.{2}}
    (i : (ColorModel.atomic P).Inst ℓ s) :
    (ColorModel.atomic P).instHval i = fun x : Fin 0 => x.elim0 := rfl

/-- **Anchor**: the atomic model's flat generator is the
computed generator `genPoly`, as already defined. -/
theorem atomic_flatGen_eq_genPoly (P : PolyProfile n m)
    (V : MvPolynomial (Fin n) ℚ) :
    (ColorModel.atomic P).flatGen PUnit.unit V = genPoly P V := by
  show contOp P.f P.gram (bind₁ X V)
      - P.kill * bind₁ X V
      + (∑ ℓ : Fin P.legs.length, ∑ _i : PUnit.{1},
          bind₁ (Sum.elim (fun x : Fin 0 => x.elim0) X)
              (rename Sum.inr (P.legs.get ℓ).1)
            * ((∑ c : Fin (P.legs.get ℓ).2.length,
                  C ((P.legs.get ℓ).2.get c).1
                    * bind₁ (((P.legs.get ℓ).2.get c).2) (bind₁ X V))
                - bind₁ X V))
      = genPoly P V
  simp only [bind₁_elim_inr, bind₁_X_self]
  have hjumps : (∑ ℓ : Fin P.legs.length, ∑ _i : PUnit.{1},
        (P.legs.get ℓ).1
          * ((∑ c, C ((P.legs.get ℓ).2.get c).1
                * bind₁ (((P.legs.get ℓ).2.get c).2) V) - V))
      = (P.legs.map fun lm => lm.1 * (transferMix lm.2 V - V)).sum := by
    conv_rhs => rw [← List.ofFn_get P.legs]
    rw [List.map_ofFn, List.sum_ofFn]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [Fintype.sum_unique]
    simp only [Function.comp_apply]
    congr 1
    congr 1
    unfold transferMix
    conv_rhs => rw [← List.ofFn_get (P.legs.get ℓ).2]
    rw [List.map_ofFn, List.sum_ofFn]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Function.comp_apply]
  rw [hjumps]
  unfold genPoly contOp
  ring

end Atomic

/-! ## 4. Bag strata and the unified jump machinery

Post-jump token types are subtype ⊕ births — never a dependent update
of a stratum assignment — which keeps every construction cast-free
(the one `dite`-cast in `bagGram` is self-busting on the diagonal). -/

section BagShapes

/-- A bag stratum: a finite token index with a stratum assignment per
token. The T-DESC "marking-space-indexed family" is the family of
these, ∀-quantified and never enumerated. -/
structure BagShape (Shape : Type 1) : Type 1 where
  /-- token index type -/
  T : Type
  [instF : Fintype T]
  [instD : DecidableEq T]
  /-- each token's stratum -/
  strat : T → Shape

attribute [instance] BagShape.instF BagShape.instD

variable {Shape : Type 1}

/-- The one-token selection embedding. -/
@[reducible] def singleEmb {α : Type} (t : α) : Fin 1 ↪ α :=
  ⟨fun _ => t, fun x y _ => Subsingleton.elim x y⟩

/-- Post-jump bag stratum: survivors of the consumed tuple keep their
strata; `b` fresh tokens are born at the given strata. Count-changing
edges (delta 1) live here. -/
def jumpShape (S : BagShape Shape) {a b : ℕ} (e : Fin a ↪ S.T)
    (bs : Fin b → Shape) : BagShape Shape where
  T := {t : S.T // ∀ r, e r ≠ t} ⊕ Fin b
  strat := Sum.elim (fun t' => S.strat t'.1) bs

/-- Splitting a full-token sum into survivors and the consumed tuple. -/
theorem sum_survivors {α : Type} [Fintype α] [DecidableEq α] {a : ℕ}
    (e : Fin a ↪ α) {A : Type*} [AddCommGroup A] (F : α → A) :
    (∑ t' : {t : α // ∀ r, e r ≠ t}, F t'.1)
      = (∑ t, F t) - ∑ r, F (e r) := by
  have hsub : (∑ t' : {t : α // ∀ r, e r ≠ t}, F t'.1)
      = ∑ t ∈ Finset.univ.filter (fun t => ∀ r, e r ≠ t), F t :=
    (Finset.sum_subtype (Finset.univ.filter fun t => ∀ r, e r ≠ t)
      (fun t => by simp) F).symm
  have himg : Finset.univ.filter (fun t : α => ¬ ∀ r, e r ≠ t)
      = Finset.univ.image e := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, not_forall, not_ne_iff]
  have himgsum : (∑ t ∈ Finset.univ.image e, F t) = ∑ r, F (e r) :=
    Finset.sum_image fun x _ y _ h => e.injective h
  have hall : (∑ t, F t)
      = (∑ t ∈ Finset.univ.filter (fun t => ∀ r, e r ≠ t), F t)
        + ∑ t ∈ Finset.univ.filter (fun t : α => ¬ ∀ r, e r ≠ t), F t :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ _ F).symm
  rw [hsub, hall, himg, himgsum]
  abel

/-- Summing over one-token selections is summing over tokens. -/
theorem sum_emb_fin_one {α : Type} [Fintype α] [DecidableEq α]
    {A : Type*} [AddCommMonoid A] (F : (Fin 1 ↪ α) → A) :
    ∑ e : Fin 1 ↪ α, F e = ∑ t : α, F (singleEmb t) := by
  have hequiv : ∀ e : Fin 1 ↪ α, singleEmb (e 0) = e := by
    intro e
    ext r
    have hr : r = 0 := Subsingleton.elim r 0
    rw [hr]
    rfl
  exact Fintype.sum_equiv
    ⟨fun e => e 0, fun t => singleEmb t, fun e => hequiv e, fun t => rfl⟩
    F (fun t => F (singleEmb t)) (fun e => congrArg F (hequiv e).symm)

end BagShapes

/-! ## 5. Pools, token embeddings, and the pool-shift engine -/

namespace ColorModel

variable {Shape : Type 1} {κ : Type} [Fintype κ] [DecidableEq κ]
variable {κ' : Type} [Fintype κ'] [DecidableEq κ']
variable (M : ColorModel Shape κ)

/-- The flat state of a bag stratum: disjoint union of the tokens'
flat states. -/
abbrev bagSt (S : BagShape Shape) : Type := (t : S.T) × M.st (S.strat t)

/-- Placing one token's observable into the bag state. -/
noncomputable def tokEmb (S : BagShape Shape) (t : S.T) :
    MvPolynomial (M.st (S.strat t)) ℚ →ₐ[ℚ] MvPolynomial (M.bagSt S) ℚ :=
  rename fun i => (⟨t, i⟩ : M.bagSt S)

theorem tokEmb_apply (S : BagShape Shape) (t : S.T)
    (ψ : MvPolynomial (M.st (S.strat t)) ℚ) :
    M.tokEmb S t ψ = rename (fun i => (⟨t, i⟩ : M.bagSt S)) ψ := rfl

theorem sigmaMk_injective (S : BagShape Shape) (t : S.T) :
    Function.Injective fun i : M.st (S.strat t) => (⟨t, i⟩ : M.bagSt S) := by
  intro i i' h
  rw [Sigma.mk.injEq] at h
  exact eq_of_heq h.2

theorem pderiv_tokEmb_same (S : BagShape Shape) (t : S.T)
    (i : M.st (S.strat t)) (ψ : MvPolynomial (M.st (S.strat t)) ℚ) :
    pderiv (⟨t, i⟩ : M.bagSt S) (M.tokEmb S t ψ)
      = M.tokEmb S t (pderiv i ψ) :=
  pderiv_rename (M.sigmaMk_injective S t) i ψ

theorem pderiv_tokEmb_ne (S : BagShape Shape) {t t' : S.T} (h : t' ≠ t)
    (i : M.st (S.strat t)) (ψ : MvPolynomial (M.st (S.strat t')) ℚ) :
    pderiv (⟨t, i⟩ : M.bagSt S) (M.tokEmb S t' ψ) = 0 :=
  pderiv_rename_of_notMem (fun _ hx => h (congrArg Sigma.fst hx)) ψ

/-- Reindexing a bag-state sum as tokens-then-coordinates. -/
theorem sum_bagSt (S : BagShape Shape) {A : Type*} [AddCommMonoid A]
    (F : M.bagSt S → A) : ∑ v, F v = ∑ t, ∑ i, F ⟨t, i⟩ := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]

/-- The pooled compile of a feature polynomial: each token contributes
its own stratum's compiled reading. -/
noncomputable def poolC (S : BagShape Shape) (φ : MvPolynomial κ ℚ) :
    MvPolynomial (M.bagSt S) ℚ :=
  ∑ t : S.T, M.tokEmb S t (bind₁ (M.χ (S.strat t)) φ)

/-- The bag compile of a dictionary: pooled compiled features. -/
noncomputable def bagCompile (Φ : κ' → MvPolynomial κ ℚ) (S : BagShape Shape) :
    κ' → MvPolynomial (M.bagSt S) ℚ :=
  fun j' => M.poolC S (Φ j')

theorem pderiv_poolC (S : BagShape Shape) (t : S.T) (i : M.st (S.strat t))
    (φ : MvPolynomial κ ℚ) :
    pderiv (⟨t, i⟩ : M.bagSt S) (M.poolC S φ)
      = M.tokEmb S t (pderiv i (bind₁ (M.χ (S.strat t)) φ)) := by
  unfold poolC
  rw [map_sum, Finset.sum_eq_single t]
  · exact M.pderiv_tokEmb_same S t i _
  · exact fun t' _ hne => M.pderiv_tokEmb_ne S hne i _
  · exact fun h => absurd (Finset.mem_univ t) h

theorem poolC_sum {ι : Type} (S : BagShape Shape) (s : Finset ι)
    (f : ι → MvPolynomial κ ℚ) :
    M.poolC S (∑ k ∈ s, f k) = ∑ k ∈ s, M.poolC S (f k) := by
  unfold poolC
  calc (∑ t, M.tokEmb S t (bind₁ (M.χ (S.strat t)) (∑ k ∈ s, f k)))
      = ∑ t, ∑ k ∈ s, M.tokEmb S t (bind₁ (M.χ (S.strat t)) (f k)) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [map_sum, map_sum]
    _ = ∑ k ∈ s, ∑ t, M.tokEmb S t (bind₁ (M.χ (S.strat t)) (f k)) :=
        Finset.sum_comm

theorem poolC_C_mul (S : BagShape Shape) (a : ℚ) (φ : MvPolynomial κ ℚ) :
    M.poolC S (C a * φ) = C a * M.poolC S φ := by
  unfold poolC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [algHom_C_mul, algHom_C_mul]

omit [Fintype κ'] [DecidableEq κ'] in
/-- Pooling a linear combination of dictionary features is the compile
of the corresponding linear polynomial — the mechanism by which the
closure witnesses (`dRep`/`GRep`, the spec-dictionary closure rows)
cash out. -/
theorem poolC_linear (S : BagShape Shape) (Φ : κ' → MvPolynomial κ ℚ)
    (d : κ' →₀ ℚ) :
    M.poolC S (d.sum fun k a => C a * Φ k)
      = bind₁ (M.bagCompile Φ S) (d.sum fun k a => C a * X k) := by
  simp only [Finsupp.sum]
  rw [poolC_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [poolC_C_mul, algHom_C_mul, bind₁_X_right]
  rfl

/-- The flat transfer kernel of a jump: survivors keep their
coordinates; born tokens read their birth kernels. -/
noncomputable def jumpKer (S : BagShape Shape) {a b : ℕ} (e : Fin a ↪ S.T)
    {bs : Fin b → Shape}
    (bker : (p : Fin b) → M.st (bs p) → MvPolynomial (M.bagSt S) ℚ) :
    M.bagSt (jumpShape S e bs) → MvPolynomial (M.bagSt S) ℚ
  | ⟨Sum.inl t', i⟩ => X ⟨t'.1, i⟩
  | ⟨Sum.inr p, i⟩ => bker p i

theorem bind₁_jumpKer_tokEmb_surv (S : BagShape Shape) {a b : ℕ}
    (e : Fin a ↪ S.T) {bs : Fin b → Shape}
    (bker : (p : Fin b) → M.st (bs p) → MvPolynomial (M.bagSt S) ℚ)
    (t' : {t : S.T // ∀ r, e r ≠ t})
    (ψ : MvPolynomial (M.st (S.strat t'.1)) ℚ) :
    bind₁ (M.jumpKer S e bker) (M.tokEmb (jumpShape S e bs) (Sum.inl t') ψ)
      = M.tokEmb S t'.1 ψ :=
  calc bind₁ (M.jumpKer S e bker) (M.tokEmb (jumpShape S e bs) (Sum.inl t') ψ)
      = bind₁ (fun i => X (⟨t'.1, i⟩ : M.bagSt S)) ψ := by
        rw [tokEmb_apply, bind₁_rename]
        rfl
    _ = rename (fun i => (⟨t'.1, i⟩ : M.bagSt S)) ψ :=
        DFunLike.congr_fun (bind₁_X_comp fun i => (⟨t'.1, i⟩ : M.bagSt S)) ψ
    _ = M.tokEmb S t'.1 ψ := rfl

theorem bind₁_jumpKer_tokEmb_born (S : BagShape Shape) {a b : ℕ}
    (e : Fin a ↪ S.T) {bs : Fin b → Shape}
    (bker : (p : Fin b) → M.st (bs p) → MvPolynomial (M.bagSt S) ℚ)
    (p : Fin b) (ψ : MvPolynomial (M.st (bs p)) ℚ) :
    bind₁ (M.jumpKer S e bker) (M.tokEmb (jumpShape S e bs) (Sum.inr p) ψ)
      = bind₁ (bker p) ψ := by
  rw [tokEmb_apply, bind₁_rename]
  rfl

/-- **The pool-shift engine**: transferring a pooled feature across a
jump reads survivors' pools, loses the consumed tuple's contributions,
and gains the born tokens' — variable plumbing only, no coherence
hypotheses. Every jump face below factors through this. -/
theorem bind₁_jumpKer_poolC (S : BagShape Shape) {a b : ℕ}
    (e : Fin a ↪ S.T) (bs : Fin b → Shape)
    (bker : (p : Fin b) → M.st (bs p) → MvPolynomial (M.bagSt S) ℚ)
    (φ : MvPolynomial κ ℚ) :
    bind₁ (M.jumpKer S e bker) (M.poolC (jumpShape S e bs) φ)
      = M.poolC S φ
        - (∑ r, M.tokEmb S (e r) (bind₁ (M.χ (S.strat (e r))) φ))
        + ∑ p, bind₁ (bker p) (bind₁ (M.χ (bs p)) φ) := by
  have hexp : bind₁ (M.jumpKer S e bker) (M.poolC (jumpShape S e bs) φ)
      = ∑ w : (jumpShape S e bs).T,
          bind₁ (M.jumpKer S e bker)
            (M.tokEmb (jumpShape S e bs) w
              (bind₁ (M.χ ((jumpShape S e bs).strat w)) φ)) := by
    unfold poolC
    rw [map_sum]
  have hsplit : (∑ w : (jumpShape S e bs).T,
        bind₁ (M.jumpKer S e bker)
          (M.tokEmb (jumpShape S e bs) w
            (bind₁ (M.χ ((jumpShape S e bs).strat w)) φ)))
      = (∑ t' : {t : S.T // ∀ r, e r ≠ t},
          bind₁ (M.jumpKer S e bker)
            (M.tokEmb (jumpShape S e bs) (Sum.inl t')
              (bind₁ (M.χ ((jumpShape S e bs).strat (Sum.inl t'))) φ)))
        + ∑ p : Fin b,
            bind₁ (M.jumpKer S e bker)
              (M.tokEmb (jumpShape S e bs) (Sum.inr p)
                (bind₁ (M.χ ((jumpShape S e bs).strat (Sum.inr p))) φ)) :=
    Fintype.sum_sum_type _
  rw [hexp, hsplit]
  have hsurv : ∀ t' : {t : S.T // ∀ r, e r ≠ t},
      bind₁ (M.jumpKer S e bker)
        (M.tokEmb (jumpShape S e bs) (Sum.inl t')
          (bind₁ (M.χ ((jumpShape S e bs).strat (Sum.inl t'))) φ))
      = M.tokEmb S t'.1 (bind₁ (M.χ (S.strat t'.1)) φ) :=
    fun t' => M.bind₁_jumpKer_tokEmb_surv S e bker t' _
  have hborn : ∀ p : Fin b,
      bind₁ (M.jumpKer S e bker)
        (M.tokEmb (jumpShape S e bs) (Sum.inr p)
          (bind₁ (M.χ ((jumpShape S e bs).strat (Sum.inr p))) φ))
      = bind₁ (bker p) (bind₁ (M.χ (bs p)) φ) :=
    fun p => M.bind₁_jumpKer_tokEmb_born S e bker p _
  rw [Finset.sum_congr rfl fun t' _ => hsurv t',
    Finset.sum_congr rfl fun p _ => hborn p,
    sum_survivors e fun t => M.tokEmb S t (bind₁ (M.χ (S.strat t)) φ)]
  unfold poolC
  rfl

/-! ## 6. The bag flat fields and their block-collection lemmas -/

/-- The bag flat drift: per-token. -/
noncomputable def bagDrift (S : BagShape Shape) :
    M.bagSt S → MvPolynomial (M.bagSt S) ℚ :=
  fun v => M.tokEmb S v.1 (M.fDrift (S.strat v.1) v.2)

/-- The bag flat gram: block-diagonal (per-token independent drivers;
the cross-token common-noise extension is deliberately not taken). -/
noncomputable def bagGram (S : BagShape Shape) :
    M.bagSt S → M.bagSt S → MvPolynomial (M.bagSt S) ℚ :=
  fun v v' =>
    if h : v'.1 = v.1 then
      M.tokEmb S v.1 (M.fGram (S.strat v.1) v.2 (h ▸ v'.2))
    else 0

theorem bagGram_mk_same (S : BagShape Shape) (t : S.T)
    (i i' : M.st (S.strat t)) :
    M.bagGram S ⟨t, i⟩ ⟨t, i'⟩ = M.tokEmb S t (M.fGram (S.strat t) i i') := by
  unfold bagGram
  rw [dif_pos rfl]

theorem bagGram_mk_ne (S : BagShape Shape) {t t' : S.T} (h : t' ≠ t)
    (i : M.st (S.strat t)) (i' : M.st (S.strat t')) :
    M.bagGram S ⟨t, i⟩ ⟨t', i'⟩ = 0 := by
  unfold bagGram
  rw [dif_neg h]

set_option maxHeartbeats 800000 in
/-- Per-token block collection of the continuous operator on a pool. -/
theorem contOp_block (S : BagShape Shape) (φ : MvPolynomial κ ℚ) :
    contOp (M.bagDrift S) (M.bagGram S) (M.poolC S φ)
      = ∑ t, M.tokEmb S t
          (contOp (M.fDrift (S.strat t)) (M.fGram (S.strat t))
            (bind₁ (M.χ (S.strat t)) φ)) := by
  unfold contOp
  have hdrift : (∑ v, M.bagDrift S v * pderiv v (M.poolC S φ))
      = ∑ t, M.tokEmb S t (∑ i, M.fDrift (S.strat t) i
          * pderiv i (bind₁ (M.χ (S.strat t)) φ)) := by
    rw [M.sum_bagSt S]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, M.pderiv_poolC S t i φ]
    rfl
  have hhess : (∑ v, ∑ v', M.bagGram S v v'
        * pderiv v (pderiv v' (M.poolC S φ)))
      = ∑ t, M.tokEmb S t (∑ i, ∑ i', M.fGram (S.strat t) i i'
          * pderiv i (pderiv i' (bind₁ (M.χ (S.strat t)) φ))) := by
    rw [M.sum_bagSt S]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hinner : ∀ i : M.st (S.strat t),
        (∑ v', M.bagGram S ⟨t, i⟩ v' * pderiv (⟨t, i⟩ : M.bagSt S) (pderiv v' (M.poolC S φ)))
        = ∑ i', M.tokEmb S t (M.fGram (S.strat t) i i')
            * M.tokEmb S t (pderiv i (pderiv i' (bind₁ (M.χ (S.strat t)) φ))) := by
      intro i
      rw [M.sum_bagSt S]
      rw [Finset.sum_eq_single t]
      · refine Finset.sum_congr rfl fun i' _ => ?_
        rw [M.bagGram_mk_same S t i i', M.pderiv_poolC S t i' φ,
          M.pderiv_tokEmb_same S t i]
      · intro t' _ hne
        refine Finset.sum_eq_zero fun i' _ => ?_
        rw [M.bagGram_mk_ne S hne i i', zero_mul]
      · exact fun h => absurd (Finset.mem_univ t) h
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hinner i]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun i' _ => by rw [map_mul]
  rw [hdrift, hhess, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_add, algHom_C_mul]

set_option maxHeartbeats 800000 in
/-- Per-token block collection of the carré on pools. -/
theorem gramOp_block (S : BagShape Shape) (φ ψ : MvPolynomial κ ℚ) :
    gramOp (M.bagGram S) (M.poolC S φ) (M.poolC S ψ)
      = ∑ t, M.tokEmb S t
          (gramOp (M.fGram (S.strat t)) (bind₁ (M.χ (S.strat t)) φ)
            (bind₁ (M.χ (S.strat t)) ψ)) := by
  unfold gramOp
  rw [M.sum_bagSt S]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hinner : ∀ i : M.st (S.strat t),
      (∑ v', M.bagGram S ⟨t, i⟩ v' * pderiv (⟨t, i⟩ : M.bagSt S) (M.poolC S φ)
          * pderiv v' (M.poolC S ψ))
      = ∑ i', M.tokEmb S t (M.fGram (S.strat t) i i')
          * M.tokEmb S t (pderiv i (bind₁ (M.χ (S.strat t)) φ))
          * M.tokEmb S t (pderiv i' (bind₁ (M.χ (S.strat t)) ψ)) := by
    intro i
    rw [M.sum_bagSt S]
    rw [Finset.sum_eq_single t]
    · refine Finset.sum_congr rfl fun i' _ => ?_
      rw [M.bagGram_mk_same S t i i', M.pderiv_poolC S t i φ,
        M.pderiv_poolC S t i' ψ]
    · intro t' _ hne
      refine Finset.sum_eq_zero fun i' _ => ?_
      rw [M.bagGram_mk_ne S hne i i', zero_mul, zero_mul]
    · exact fun h => absurd (Finset.mem_univ t) h
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hinner i]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [map_mul, map_mul]

end ColorModel

/-! ## 7. Bag edges and the lift -/

namespace ColorModel

variable {Shape : Type 1} {κ : Type} [Fintype κ] [DecidableEq κ]
variable {κ' : Type} [Fintype κ'] [DecidableEq κ']

/-- The selected tuple's feature values, embedded at their tokens. -/
noncomputable def tupleVal (M : ColorModel Shape κ) (S : BagShape Shape)
    {a : ℕ} (e : Fin a ↪ S.T) :
    Fin a × κ → MvPolynomial (M.bagSt S) ℚ :=
  fun rj => M.tokEmb S (e rj.1) (M.χ (S.strat (e rj.1)) rj.2)

/-- A bag-level edge family (delta 1 + delta 2): consume an injective
`a`-tuple, birth `b` tokens. The rate reads (tuple features ⊕
aggregates) — T1's vocabulary, mean-field rates included. Births carry
claimed features (`bg`, presentation level) and flat kernels (`bKer`)
with per-feature coherence (`hbKer`). Read arcs are
consume+identical-rebirth; a color-level kill is the `a = 1, b = 0`
case (G-H1 absorption, folded in by `bag` below). -/
structure BagEdge (M : ColorModel Shape κ)
    (κ' : Type) [Fintype κ'] [DecidableEq κ']
    (Φ : κ' → MvPolynomial κ ℚ) : Type 1 where
  a : ℕ
  b : ℕ
  rate : MvPolynomial ((Fin a × κ) ⊕ κ') ℚ
  MixIx : Type
  [instMix : Fintype MixIx]
  w : MixIx → ℚ
  bStrat : MixIx → Fin b → Shape
  bg : MixIx → Fin b → κ → MvPolynomial ((Fin a × κ) ⊕ κ') ℚ
  bKer : (S : BagShape Shape) → (Fin a ↪ S.T) → (c : MixIx) → (p : Fin b) →
    M.st (bStrat c p) → MvPolynomial (M.bagSt S) ℚ
  hbKer : ∀ (S : BagShape Shape) (e : Fin a ↪ S.T) (c : MixIx) (p : Fin b)
    (j : κ), bind₁ (bKer S e c p) (M.χ (bStrat c p) j)
      = bind₁ (Sum.elim (M.tupleVal S e) (M.bagCompile Φ S)) (bg c p j)

attribute [instance] BagEdge.instMix

variable (M : ColorModel Shape κ)

/-- `tokEmb` post-composition on a substitution family. -/
theorem bind₁_tokEmb_comp (S : BagShape Shape) (t : S.T) {σ : Type}
    (g : σ → MvPolynomial (M.st (S.strat t)) ℚ) (p : MvPolynomial σ ℚ) :
    bind₁ (fun j => M.tokEmb S t (g j)) p = M.tokEmb S t (bind₁ g p) := by
  rw [tokEmb_apply, rename_bind₁]
  rfl

/-- Single-token pool shift (the arity-1 specialization the inner-leg
and kill faces use). -/
theorem bind₁_jumpKer_poolC_single (S : BagShape Shape) (t : S.T) {b : ℕ}
    (bs : Fin b → Shape)
    (bker : (p : Fin b) → M.st (bs p) → MvPolynomial (M.bagSt S) ℚ)
    (φ : MvPolynomial κ ℚ) :
    bind₁ (M.jumpKer S (singleEmb t) bker)
      (M.poolC (jumpShape S (singleEmb t) bs) φ)
      = M.poolC S φ - M.tokEmb S t (bind₁ (M.χ (S.strat t)) φ)
        + ∑ p, bind₁ (bker p) (bind₁ (M.χ (bs p)) φ) := by
  have hsingle : (∑ r, M.tokEmb S (singleEmb t r)
        (bind₁ (M.χ (S.strat (singleEmb t r))) φ))
      = M.tokEmb S t (bind₁ (M.χ (S.strat t)) φ) := by
    rw [Fin.sum_univ_one]
    rfl
  rw [M.bind₁_jumpKer_poolC S (singleEmb t) bs bker φ, hsingle]

/-! ### The three lifted-leg coherence faces

Each is the pool-shift engine plus the relevant input coherence: the
lifted inner leg concatenates the distinguished path (delta 3), the
bag edge consumes a tuple and births (deltas 1–2), and the kill
promotion is G-H1 absorption. The statements are written to match the
`bag` construction's fields verbatim. -/

omit [Fintype κ'] [DecidableEq κ'] in
theorem lift_inner_coherence (S : BagShape Shape)
    (Φ : κ' → MvPolynomial κ ℚ) (t : S.T) {ℓ : M.LegIx}
    (i₀ : M.Inst ℓ (S.strat t)) (c : M.legMix ℓ) (j' : κ') :
    bind₁ (M.jumpKer S (singleEmb t)
        (fun _ : Fin 1 => fun x => M.tokEmb S t (M.instKer i₀ c x)))
      (M.poolC (jumpShape S (singleEmb t) (fun _ : Fin 1 => M.instTgt i₀ c))
        (Φ j'))
      = bind₁ (Sum.elim
          (Sum.elim (fun x => M.tokEmb S t (M.instHval i₀ x))
            (fun j => M.tokEmb S t (M.χ (S.strat t) j)))
          (M.bagCompile Φ S))
        (X (Sum.inr j') - rename (Sum.inl ∘ Sum.inr) (Φ j')
          + bind₁ (fun j => rename Sum.inl (M.legG ℓ c j)) (Φ j')) := by
  have hEcomp : ∀ p : MvPolynomial (M.legE ℓ ⊕ κ) ℚ,
      bind₁ (Sum.elim (fun x => M.tokEmb S t (M.instHval i₀ x))
        (fun j => M.tokEmb S t (M.χ (S.strat t) j))) p
      = M.tokEmb S t (bind₁ (Sum.elim (M.instHval i₀) (M.χ (S.strat t))) p) := by
    intro p
    have helim : (Sum.elim (fun x => M.tokEmb S t (M.instHval i₀ x))
          (fun j => M.tokEmb S t (M.χ (S.strat t) j)))
        = fun y => M.tokEmb S t (Sum.elim (M.instHval i₀) (M.χ (S.strat t)) y) := by
      funext y
      cases y <;> rfl
    rw [helim, M.bind₁_tokEmb_comp S t]
  rw [M.bind₁_jumpKer_poolC_single S t (fun _ : Fin 1 => M.instTgt i₀ c)
    (fun _ : Fin 1 => fun x => M.tokEmb S t (M.instKer i₀ c x)) (Φ j')]
  rw [Fin.sum_univ_one, M.bind₁_tokEmb_comp S t (M.instKer i₀ c),
    M.instKer_compile i₀ c (Φ j')]
  rw [map_add, map_sub, bind₁_X_right]
  have hmid : bind₁ (Sum.elim
        (Sum.elim (fun x => M.tokEmb S t (M.instHval i₀ x))
          (fun j => M.tokEmb S t (M.χ (S.strat t) j)))
        (M.bagCompile Φ S)) (rename (Sum.inl ∘ Sum.inr) (Φ j'))
      = M.tokEmb S t (bind₁ (M.χ (S.strat t)) (Φ j')) := by
    rw [bind₁_rename]
    exact M.bind₁_tokEmb_comp S t (M.χ (S.strat t)) (Φ j')
  have hlast : bind₁ (Sum.elim
        (Sum.elim (fun x => M.tokEmb S t (M.instHval i₀ x))
          (fun j => M.tokEmb S t (M.χ (S.strat t) j)))
        (M.bagCompile Φ S))
        (bind₁ (fun j => rename Sum.inl (M.legG ℓ c j)) (Φ j'))
      = M.tokEmb S t (bind₁ (Sum.elim (M.instHval i₀) (M.χ (S.strat t)))
          (bind₁ (M.legG ℓ c) (Φ j'))) := by
    rw [bind₁_bind₁]
    have hper : (fun j => bind₁ (Sum.elim
          (Sum.elim (fun x => M.tokEmb S t (M.instHval i₀ x))
            (fun j => M.tokEmb S t (M.χ (S.strat t) j)))
          (M.bagCompile Φ S)) (rename Sum.inl (M.legG ℓ c j)))
        = fun j => M.tokEmb S t
            (bind₁ (Sum.elim (M.instHval i₀) (M.χ (S.strat t))) (M.legG ℓ c j)) := by
      funext j
      rw [bind₁_elim_inl, hEcomp]
    rw [hper, M.bind₁_tokEmb_comp S t, bind₁_bind₁]
  rw [hmid, hlast]
  rfl

omit [Fintype κ'] [DecidableEq κ'] in
theorem kill_coherence (S : BagShape Shape) (Φ : κ' → MvPolynomial κ ℚ)
    (t : S.T) (j' : κ') :
    bind₁ (M.jumpKer S (singleEmb t) (fun p : Fin 0 => p.elim0))
      (M.poolC (jumpShape S (singleEmb t) (fun p : Fin 0 => p.elim0)) (Φ j'))
      = bind₁ (Sum.elim (fun j => M.tokEmb S t (M.χ (S.strat t) j))
          (M.bagCompile Φ S))
        (X (Sum.inr j') - rename Sum.inl (Φ j')) := by
  rw [M.bind₁_jumpKer_poolC_single S t (fun p : Fin 0 => p.elim0)
    (fun p : Fin 0 => p.elim0) (Φ j')]
  rw [Fin.sum_univ_zero, add_zero, map_sub, bind₁_X_right, bind₁_elim_inl,
    M.bind₁_tokEmb_comp S t (M.χ (S.strat t)) (Φ j')]
  rfl

theorem edge_coherence (S : BagShape Shape) (Φ : κ' → MvPolynomial κ ℚ)
    (E : M.BagEdge κ' Φ) (e : Fin E.a ↪ S.T) (c : E.MixIx) (j' : κ') :
    bind₁ (M.jumpKer S e (E.bKer S e c))
      (M.poolC (jumpShape S e (E.bStrat c)) (Φ j'))
      = bind₁ (Sum.elim (M.tupleVal S e) (M.bagCompile Φ S))
        (X (Sum.inr j')
          - (∑ r, rename (fun j => Sum.inl (r, j)) (Φ j'))
          + ∑ p, bind₁ (E.bg c p) (Φ j')) := by
  rw [M.bind₁_jumpKer_poolC S e (E.bStrat c) (E.bKer S e c) (Φ j')]
  have hcons : ∀ r : Fin E.a,
      bind₁ (Sum.elim (M.tupleVal S e) (M.bagCompile Φ S))
        (rename (fun j => Sum.inl (r, j)) (Φ j'))
      = M.tokEmb S (e r) (bind₁ (M.χ (S.strat (e r))) (Φ j')) := by
    intro r
    rw [bind₁_rename]
    exact M.bind₁_tokEmb_comp S (e r) (M.χ (S.strat (e r))) (Φ j')
  have hborn : ∀ p : Fin E.b,
      bind₁ (Sum.elim (M.tupleVal S e) (M.bagCompile Φ S))
        (bind₁ (E.bg c p) (Φ j'))
      = bind₁ (E.bKer S e c p) (bind₁ (M.χ (E.bStrat c p)) (Φ j')) := by
    intro p
    rw [bind₁_bind₁, bind₁_bind₁]
    have hfun : (fun j => bind₁ (Sum.elim (M.tupleVal S e) (M.bagCompile Φ S))
          (E.bg c p j))
        = fun j => bind₁ (E.bKer S e c p) (M.χ (E.bStrat c p) j) :=
      funext fun j => (E.hbKer S e c p j).symm
    rw [hfun]
  rw [map_add, map_sub, bind₁_X_right, map_sum, map_sum,
    Finset.sum_congr rfl fun r _ => hcons r,
    Finset.sum_congr rfl fun p _ => hborn p]
  rfl

/-! ## 8. The lift, and the square -/

/-- **The Bag lift**, as a map of presentations: consumes a
Mechanism-shaped color model, a dictionary, bag edge families, and
the linear closure witnesses (`dRep`/`GRep` — the spec-dictionary
closure rows); returns
the lifted model over bag strata. **The output re-enters as input**
(delta 3: closure of the interface under the lift); nesting is
function composition. The input's `pKill` is folded in as an arity-1
removal leg (G-H1 absorption: kill at level n = ordinary next at level
n+1); the output is conservative. Lifted inner legs concatenate
distinguished paths (`legE' = legE ⊕ κ`); bag edges select injective
tuples (`Fin a ↪ S.T`, delta 2); count motion rides the dictionary
(delta 1: a consumed token's features leave the pools — the constant
feature's pool is the count, so deaths decrement it; the
SwitchEdge-self-loop reading, visible in the shift polynomials). -/
noncomputable def bag
    (Φ : κ' → MvPolynomial κ ℚ)
    (EdgeIx : Type) [Fintype EdgeIx] (edge : EdgeIx → M.BagEdge κ' Φ)
    (dRep : κ' → κ' →₀ ℚ)
    (hdRep : ∀ j', M.contRead (Φ j') = (dRep j').sum fun k a => C a * Φ k)
    (GRep : κ' → κ' → κ' →₀ ℚ)
    (hGRep : ∀ j' l',
      M.gramRead (Φ j') (Φ l') = (GRep j' l').sum fun k a => C a * Φ k) :
    ColorModel (BagShape Shape) κ' where
  st := M.bagSt
  χ := M.bagCompile Φ
  pDrift j' := (dRep j').sum fun k a => C a * X k
  pGram j' l' := (GRep j' l').sum fun k a => C a * X k
  pKill := 0
  LegIx := M.LegIx ⊕ (EdgeIx ⊕ Unit)
  legE := fun ℓ' => match ℓ' with
    | .inl ℓ => M.legE ℓ ⊕ κ
    | .inr (.inl ε) => Fin (edge ε).a × κ
    | .inr (.inr _) => κ
  instLegEF := fun ℓ' => match ℓ' with
    | .inl ℓ => inferInstanceAs (Fintype (M.legE ℓ ⊕ κ))
    | .inr (.inl ε) => inferInstanceAs (Fintype (Fin (edge ε).a × κ))
    | .inr (.inr _) => inferInstanceAs (Fintype κ)
  instLegED := fun ℓ' => match ℓ' with
    | .inl ℓ => inferInstanceAs (DecidableEq (M.legE ℓ ⊕ κ))
    | .inr (.inl ε) => inferInstanceAs (DecidableEq (Fin (edge ε).a × κ))
    | .inr (.inr _) => inferInstanceAs (DecidableEq κ)
  legRate := fun ℓ' => match ℓ' with
    | .inl ℓ => rename Sum.inl (M.legRate ℓ)
    | .inr (.inl ε) => (edge ε).rate
    | .inr (.inr _) => rename Sum.inl M.pKill
  legMix := fun ℓ' => match ℓ' with
    | .inl ℓ => M.legMix ℓ
    | .inr (.inl ε) => (edge ε).MixIx
    | .inr (.inr _) => PUnit
  instLegMixF := fun ℓ' => match ℓ' with
    | .inl ℓ => inferInstanceAs (Fintype (M.legMix ℓ))
    | .inr (.inl ε) => inferInstanceAs (Fintype (edge ε).MixIx)
    | .inr (.inr _) => inferInstanceAs (Fintype PUnit)
  legW := fun ℓ' => match ℓ' with
    | .inl ℓ => M.legW ℓ
    | .inr (.inl ε) => (edge ε).w
    | .inr (.inr _) => fun _ => 1
  legG := fun ℓ' => match ℓ' with
    | .inl ℓ => fun c j' => X (Sum.inr j') - rename (Sum.inl ∘ Sum.inr) (Φ j')
        + bind₁ (fun j => rename Sum.inl (M.legG ℓ c j)) (Φ j')
    | .inr (.inl ε) => fun c j' => X (Sum.inr j')
        - (∑ r, rename (fun j => Sum.inl (r, j)) (Φ j'))
        + ∑ p, bind₁ ((edge ε).bg c p) (Φ j')
    | .inr (.inr _) => fun _ j' => X (Sum.inr j') - rename Sum.inl (Φ j')
  fDrift := M.bagDrift
  fGram := M.bagGram
  fKill _ := 0
  Inst := fun ℓ' S => match ℓ' with
    | .inl ℓ => (t : S.T) × M.Inst ℓ (S.strat t)
    | .inr (.inl ε) => Fin (edge ε).a ↪ S.T
    | .inr (.inr _) => S.T
  instInstF := fun ℓ' S => match ℓ' with
    | .inl ℓ => inferInstanceAs (Fintype ((t : S.T) × M.Inst ℓ (S.strat t)))
    | .inr (.inl ε) => inferInstanceAs (Fintype (Fin (edge ε).a ↪ S.T))
    | .inr (.inr _) => inferInstanceAs (Fintype S.T)
  instHval := fun {ℓ'} {S} => match ℓ' with
    | .inl ℓ => fun i => Sum.elim
        (fun x => M.tokEmb S i.1 (M.instHval i.2 x))
        (fun j => M.tokEmb S i.1 (M.χ (S.strat i.1) j))
    | .inr (.inl ε) => fun e => M.tupleVal S e
    | .inr (.inr _) => fun t j => M.tokEmb S t (M.χ (S.strat t) j)
  instTgt := fun {ℓ'} {S} => match ℓ' with
    | .inl ℓ => fun i c =>
        jumpShape S (singleEmb i.1) (fun _ : Fin 1 => M.instTgt i.2 c)
    | .inr (.inl ε) => fun e c => jumpShape S e ((edge ε).bStrat c)
    | .inr (.inr _) => fun t _ =>
        jumpShape S (singleEmb t) (fun p : Fin 0 => p.elim0)
  instKer := fun {ℓ'} {S} => match ℓ' with
    | .inl ℓ => fun i c => M.jumpKer S (singleEmb i.1)
        (fun _ : Fin 1 => fun x => M.tokEmb S i.1 (M.instKer i.2 c x))
    | .inr (.inl ε) => fun e c => M.jumpKer S e ((edge ε).bKer S e c)
    | .inr (.inr _) => fun t _ =>
        M.jumpKer S (singleEmb t) (fun p : Fin 0 => p.elim0)
  hDrift := fun S j' => by
    have h1 : contOp (M.bagDrift S) (M.bagGram S) (M.poolC S (Φ j'))
        = ∑ t, M.tokEmb S t
            (bind₁ (M.χ (S.strat t)) (M.contRead (Φ j'))) := by
      rw [M.contOp_block S (Φ j')]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [contOp_compile (M.fDrift (S.strat t)) (M.fGram (S.strat t))
        (M.χ (S.strat t)) M.pDrift M.pGram (M.hDrift (S.strat t))
        (M.hGram (S.strat t)) (Φ j')]
      rfl
    calc contOp (M.bagDrift S) (M.bagGram S) (M.bagCompile Φ S j')
        = ∑ t, M.tokEmb S t
            (bind₁ (M.χ (S.strat t)) (M.contRead (Φ j'))) := h1
      _ = M.poolC S (M.contRead (Φ j')) := rfl
      _ = M.poolC S ((dRep j').sum fun k a => C a * Φ k) := by rw [hdRep j']
      _ = bind₁ (M.bagCompile Φ S) ((dRep j').sum fun k a => C a * X k) :=
          M.poolC_linear S Φ (dRep j')
  hGram := fun S j' l' => by
    have h1 : gramOp (M.bagGram S) (M.poolC S (Φ j')) (M.poolC S (Φ l'))
        = ∑ t, M.tokEmb S t
            (bind₁ (M.χ (S.strat t)) (M.gramRead (Φ j') (Φ l'))) := by
      rw [M.gramOp_block S (Φ j') (Φ l')]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [gramOp_compile (M.fGram (S.strat t)) (M.χ (S.strat t)) M.pGram
        (M.hGram (S.strat t)) (Φ j') (Φ l')]
      rfl
    calc gramOp (M.bagGram S) (M.bagCompile Φ S j') (M.bagCompile Φ S l')
        = ∑ t, M.tokEmb S t
            (bind₁ (M.χ (S.strat t)) (M.gramRead (Φ j') (Φ l'))) := h1
      _ = M.poolC S (M.gramRead (Φ j') (Φ l')) := rfl
      _ = M.poolC S ((GRep j' l').sum fun k a => C a * Φ k) := by
          rw [hGRep j' l']
      _ = bind₁ (M.bagCompile Φ S) ((GRep j' l').sum fun k a => C a * X k) :=
          M.poolC_linear S Φ (GRep j' l')
  hKill := fun S => (map_zero _).symm
  hKer := fun {ℓ'} {S} i c j' => match ℓ', i, c with
    | .inl ℓ, i, c => M.lift_inner_coherence S Φ i.1 i.2 c j'
    | .inr (.inl ε), e, c => M.edge_coherence S Φ (edge ε) e c j'
    | .inr (.inr _), t, _ => M.kill_coherence S Φ t j'

/-- **THE POLYMORPHIC BAG-LIFT SQUARE** (closing the three deltas):
the flat generator of the lifted bag on a compiled
certificate IS the compile of the lifted presentation's reading —
`models_square` at `M.bag …`, at every bag stratum, with no scope
hypotheses at the target stratum. Nesting needs no further theorem:
`(M.bag …).bag …` re-enters, and depth is instantiation depth. -/
theorem bag_square
    (Φ : κ' → MvPolynomial κ ℚ)
    (EdgeIx : Type) [Fintype EdgeIx] (edge : EdgeIx → M.BagEdge κ' Φ)
    (dRep : κ' → κ' →₀ ℚ)
    (hdRep : ∀ j', M.contRead (Φ j') = (dRep j').sum fun k a => C a * Φ k)
    (GRep : κ' → κ' → κ' →₀ ℚ)
    (hGRep : ∀ j' l',
      M.gramRead (Φ j') (Φ l') = (GRep j' l').sum fun k a => C a * Φ k)
    (S : BagShape Shape) (q : MvPolynomial κ' ℚ) :
    (M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).flatGen S q
      = bind₁ ((M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).χ S)
          ((M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).contRead q
            - (M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).pKill * q)
        + ∑ ℓ, ∑ i : (M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).Inst ℓ S,
            bind₁ (Sum.elim
                ((M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).instHval i)
                ((M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).χ S))
              ((M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).dtRead ℓ q) :=
  (M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).models_square S q

/-! ### Projection lemmas for the lifted model (fixture-facing) -/

section BagProjections

variable (Φ : κ' → MvPolynomial κ ℚ)
  (EdgeIx : Type) [Fintype EdgeIx] (edge : EdgeIx → M.BagEdge κ' Φ)
  (dRep : κ' → κ' →₀ ℚ)
  (hdRep : ∀ j', M.contRead (Φ j') = (dRep j').sum fun k a => C a * Φ k)
  (GRep : κ' → κ' → κ' →₀ ℚ)
  (hGRep : ∀ j' l',
    M.gramRead (Φ j') (Φ l') = (GRep j' l').sum fun k a => C a * Φ k)

@[simp] theorem bag_χ :
    (M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).χ = M.bagCompile Φ := rfl

@[simp] theorem bag_pDrift (j' : κ') :
    (M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).pDrift j'
      = (dRep j').sum fun k a => C a * X k := rfl

@[simp] theorem bag_pGram (j' l' : κ') :
    (M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).pGram j' l'
      = (GRep j' l').sum fun k a => C a * X k := rfl

@[simp] theorem bag_pKill :
    (M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).pKill = 0 := rfl

@[simp] theorem bag_fDrift :
    (M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).fDrift = M.bagDrift := rfl

@[simp] theorem bag_fGram :
    (M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).fGram = M.bagGram := rfl

@[simp] theorem bag_fKill (S : BagShape Shape) :
    (M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).fKill S = 0 := rfl

end BagProjections

/-! ### The μ-compat lemma (pool-of-pools = flattened pool)

`BagMonad.lean`'s `bagMu` (multiset flatten, `double-cat`; cited by
name — no cross-package import) has, at this module's polynomial
stratum, the indexed-token shadow `Equiv.sigmaAssoc`; on μ*-pulled-back
dictionaries (the outer dictionary is `X` — each outer feature the pool
of an inner aggregate), the two-level compile is the flattened
one-level compile transported along it. SCOPE: μ-flattening applies
only to the edge-free/group-blind fragment — an outer death reads
exactly the structure μ forgets; and μ-flattening ≠ GSHS-flattening
(the latter is a separate, staged development). This is the one
μ-compat lemma; the fixture checks the generator face at its
concrete cell. -/

/-- Flatten a two-level bag stratum (value-level `bagMu` at shape
level). -/
@[reducible] def muShape {Shape : Type 1} (S₂ : BagShape (BagShape Shape)) :
    BagShape Shape where
  T := (t : S₂.T) × (S₂.strat t).T
  strat := fun tk => (S₂.strat tk.1).strat tk.2

theorem mu_compat_pool (Φ : κ' → MvPolynomial κ ℚ)
    (EdgeIx : Type) [Fintype EdgeIx] (edge : EdgeIx → M.BagEdge κ' Φ)
    (dRep : κ' → κ' →₀ ℚ)
    (hdRep : ∀ j', M.contRead (Φ j') = (dRep j').sum fun k a => C a * Φ k)
    (GRep : κ' → κ' → κ' →₀ ℚ)
    (hGRep : ∀ j' l',
      M.gramRead (Φ j') (Φ l') = (GRep j' l').sum fun k a => C a * Φ k)
    (S₂ : BagShape (BagShape Shape)) (j' : κ') :
    (M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).bagCompile
        (X : κ' → MvPolynomial κ' ℚ) S₂ j'
      = rename (Equiv.sigmaAssoc fun t k => M.st ((S₂.strat t).strat k))
          (M.poolC (muShape S₂) (Φ j')) := by
  have hL : (M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).bagCompile
        (X : κ' → MvPolynomial κ' ℚ) S₂ j'
      = ∑ t : S₂.T, ∑ k : (S₂.strat t).T,
          rename (fun i : M.st ((S₂.strat t).strat k) =>
              (⟨t, ⟨k, i⟩⟩ :
                (M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).bagSt S₂))
            (bind₁ (M.χ ((S₂.strat t).strat k)) (Φ j')) := by
    show (M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).poolC S₂
        (X j' : MvPolynomial κ' ℚ) = _
    unfold poolC
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [bind₁_X_right]
    show (M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).tokEmb S₂ t
        (∑ k, M.tokEmb (S₂.strat t) k
          (bind₁ (M.χ ((S₂.strat t).strat k)) (Φ j'))) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [tokEmb_apply, tokEmb_apply]
    exact rename_rename _ _ _
  have hR : rename (Equiv.sigmaAssoc fun t k => M.st ((S₂.strat t).strat k))
        (M.poolC (muShape S₂) (Φ j'))
      = ∑ t : S₂.T, ∑ k : (S₂.strat t).T,
          rename (fun i : M.st ((S₂.strat t).strat k) =>
              (⟨t, ⟨k, i⟩⟩ :
                (M.bag Φ EdgeIx edge dRep hdRep GRep hGRep).bagSt S₂))
            (bind₁ (M.χ ((S₂.strat t).strat k)) (Φ j')) := by
    unfold poolC
    rw [map_sum, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun k _ => ?_
    rw [tokEmb_apply]
    exact rename_rename _ _ _
  rw [hL, hR]

end ColorModel

end BagLift

end Qtsl
