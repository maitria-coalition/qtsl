import Mathlib.Data.Set.Lattice

import Mathlib.Data.ENNReal.Basic

/-!
# Coarsening, upper previsions, and sampler transport

Three families of results about passing structure along a coarsening map
between state spaces, formalized at the level of sets and complete
lattices.

* **Possibilistic coarsening.**  Gluing (intersection of constraint sets)
  commutes laxly with direct image: the image of an intersection is
  contained in the intersection of the images
  (`image_glue_subset_glue_image`), and the inclusion can be strict
  (`glueTransport_strict`: two constraints on a three-component state,
  coarsened by hiding the middle component).

* **Upper previsions as envelopes.**  For evaluation maps valued in an
  arbitrary complete lattice, the upper envelope over a credal set is
  monotone in the set (`upperPrevC_mono`), satisfies exact change of
  variables along pushforward (`upperPrevC_push_image`), and yields a
  soundness statement for certificates transported along a coarsening
  (`certificate_soundness`).  The proofs are purely order-theoretic, so
  `ℝ≥0∞`-valued and signed `EReal`-valued evaluations both instantiate
  (bounded-below real gambles embed in the latter).

* **Sampler transport relations.**  Index-selection relations between
  finite families compose relationally on the nose: with a fixed index
  map (`samplerRel_comp`), with a demonically chosen index map from a
  given set (`samplerRelJ_comp`), and in bundled multiport form with one
  shared selection across all ports (`samplerRelJB_comp`).  The bundled
  relation refines the per-port-independent one
  (`samplerRelJB_subset_perPort`), and the two semantics genuinely differ
  (`perPort_ne_bundled`, a two-port counterexample).
-/

namespace DoubleCat.CrossSite

section Possibilistic

variable {Ωf Ωg : Type*} {ι : Sort*}

/-- Coarsening the glue refines the glue of the coarsenings: the direct image
of an intersection of constraint sets is contained in the intersection of the
direct images. -/
theorem image_glue_subset_glue_image (ρ : Ωf → Ωg) (A : ι → Set Ωf) :
    ρ '' (⋂ i, A i) ⊆ ⋂ i, ρ '' A i :=
  Set.image_iInter_subset A ρ

/-- The inclusion of `image_glue_subset_glue_image` can be strict: on a
three-component Boolean state with constraints "first = middle" and
"middle = last", hiding the middle component leaves the coarse state
`(true, false)` in the intersection of the images but not in the image of the
intersection. -/
theorem glueTransport_strict :
    ((true, false) ∈
        ((fun p : Bool × Bool × Bool => (p.1, p.2.2)) '' {p | p.1 = p.2.1}) ∩
        ((fun p : Bool × Bool × Bool => (p.1, p.2.2)) '' {p | p.2.1 = p.2.2})) ∧
    ((true, false) ∉
        (fun p : Bool × Bool × Bool => (p.1, p.2.2)) ''
          ({p | p.1 = p.2.1} ∩ {p | p.2.1 = p.2.2})) := by
  constructor
  · exact ⟨⟨(true, true, false), rfl, rfl⟩, ⟨(true, false, false), rfl, rfl⟩⟩
  · rintro ⟨⟨a, b, c⟩, ⟨h₁, h₂⟩, hρ⟩
    rw [Prod.mk.injEq] at hρ
    obtain ⟨ha, hc⟩ := hρ
    subst ha
    subst hc
    exact Bool.noConfusion (h₁.trans h₂)

end Possibilistic

section Prevision

variable {P Q G H : Type*} {V : Type*} [CompleteLattice V]

/-- The data for transporting upper previsions along a coarsening: fine and
coarse model types `P`, `Q` with a pushforward `push : P → Q`, fine and
coarse gamble types `G`, `H` with a pullback `pull : H → G`, evaluation maps
into a complete lattice `V`, and the compatibility law: evaluating a pulled
gamble finely agrees with evaluating it coarsely on the pushforward. -/
structure PrevisionContext (P Q G H V : Type*) where
  evF : P → G → V
  evC : Q → H → V
  push : P → Q
  pull : H → G
  change_of_variables : ∀ p h, evC (push p) h = evF p (pull h)

variable (ctx : PrevisionContext P Q G H V)

/-- The fine upper prevision: the upper envelope of the fine evaluations over
a credal set `M`. -/
noncomputable def upperPrevF (M : Set P) (g : G) : V :=
  ⨆ p ∈ M, ctx.evF p g

/-- The coarse upper prevision: the upper envelope of the coarse evaluations
over a credal set `N`. -/
noncomputable def upperPrevC (N : Set Q) (h : H) : V :=
  ⨆ q ∈ N, ctx.evC q h

/-- Upper previsions are monotone in the credal set. -/
theorem upperPrevC_mono {N N' : Set Q} (hNN : N ⊆ N') (h : H) :
    upperPrevC ctx N h ≤ upperPrevC ctx N' h := by
  refine iSup₂_le fun q hq => ?_
  exact le_iSup₂_of_le q (hNN hq) le_rfl

/-- Exact change of variables: the coarse upper prevision over the pushforward
credal set equals the fine upper prevision of the pulled-back gamble. -/
theorem upperPrevC_push_image (M : Set P) (h : H) :
    upperPrevC ctx (ctx.push '' M) h = upperPrevF ctx M (ctx.pull h) := by
  unfold upperPrevC upperPrevF
  apply le_antisymm
  · refine iSup₂_le ?_
    rintro q ⟨p, hp, rfl⟩
    rw [ctx.change_of_variables]
    exact le_iSup₂_of_le p hp le_rfl
  · refine iSup₂_le fun p hp => ?_
    rw [← ctx.change_of_variables]
    exact le_iSup₂_of_le (ctx.push p) ⟨p, hp, rfl⟩ le_rfl

/-- Certificate soundness: if the pushforward of the fine credal set is
contained in the coarse credal set, then a bound certified coarsely for a
coarse gamble is a bound finely for its pullback. -/
theorem certificate_soundness (M : Set P) (N : Set Q)
    (hincl : ctx.push '' M ⊆ N) (h : H) (bound : V)
    (hcert : upperPrevC ctx N h ≤ bound) :
    upperPrevF ctx M (ctx.pull h) ≤ bound :=
  upperPrevC_push_image ctx M h ▸ le_trans (upperPrevC_mono ctx hincl h) hcert

end Prevision

section Sampler

variable {X : Type*} {l m n : ℕ}

/-- The transport relation of a fixed index map `ι`: the coarse family reads
the fine family through `ι`. -/
def samplerRel (ι : Fin n → Fin m) : Set ((Fin m → X) × (Fin n → X)) :=
  {p | ∀ k, p.2 k = p.1 (ι k)}

/-- The jittered transport relation: some index map from `S` (demonically
chosen) relates the families. -/
def samplerRelJ (S : Set (Fin n → Fin m)) :
    Set ((Fin m → X) × (Fin n → X)) :=
  {p | ∃ ι ∈ S, ∀ k, p.2 k = p.1 (ι k)}

/-- The bundled multiport transport relation: one shared demonic index-map
selection relates the families at every port simultaneously. -/
def samplerRelJB (π : Type*) (S : Set (Fin n → Fin m)) :
    Set ((π → Fin m → X) × (π → Fin n → X)) :=
  {p | ∃ ι ∈ S, ∀ q k, p.2 q k = p.1 q (ι k)}

/-- Relational composition, in diagrammatic order. -/
def relComp (R : Set ((Fin m → X) × (Fin n → X)))
    (Q : Set ((Fin l → X) × (Fin m → X))) :
    Set ((Fin l → X) × (Fin n → X)) :=
  {p | ∃ y : Fin m → X, (p.1, y) ∈ Q ∧ (y, p.2) ∈ R}

/-- Relational composition of multiport relations. -/
def relCompB (π : Type*)
    (R : Set ((π → Fin m → X) × (π → Fin n → X)))
    (Q : Set ((π → Fin l → X) × (π → Fin m → X))) :
    Set ((π → Fin l → X) × (π → Fin n → X)) :=
  {p | ∃ y : π → Fin m → X, (p.1, y) ∈ Q ∧ (y, p.2) ∈ R}

/-- Fixed-index transport relations compose on the nose. -/
theorem samplerRel_comp (κ : Fin m → Fin l) (ι : Fin n → Fin m) :
    relComp (samplerRel (X := X) ι) (samplerRel κ) = samplerRel (κ ∘ ι) := by
  ext ⟨rf, rc⟩
  constructor
  · rintro ⟨rm, hA, hB⟩ k
    exact (hB k).trans (hA (ι k))
  · intro h
    exact ⟨fun j => rf (κ j), fun j => rfl, fun k => h k⟩

/-- Jittered transport relations compose on the nose: the composite's index
set is the pointwise composite of the index sets. -/
theorem samplerRelJ_comp (S : Set (Fin m → Fin l)) (T : Set (Fin n → Fin m)) :
    relComp (samplerRelJ (X := X) T) (samplerRelJ S) =
      samplerRelJ {γ | ∃ κ ∈ S, ∃ ι ∈ T, γ = κ ∘ ι} := by
  ext ⟨rf, rc⟩
  constructor
  · rintro ⟨rm, ⟨κ, hκS, hA⟩, ⟨ι, hιT, hB⟩⟩
    exact ⟨κ ∘ ι, ⟨κ, hκS, ι, hιT, rfl⟩, fun k => (hB k).trans (hA (ι k))⟩
  · rintro ⟨γ, ⟨κ, hκS, ι, hιT, rfl⟩, h⟩
    exact ⟨fun j => rf (κ j), ⟨κ, hκS, fun j => rfl⟩, ⟨ι, hιT, fun k => h k⟩⟩

/-- Bundled multiport transport relations compose on the nose, with one shared
selection per composition factor. -/
theorem samplerRelJB_comp {π : Type*}
    (S : Set (Fin m → Fin l)) (T : Set (Fin n → Fin m)) :
    relCompB π (samplerRelJB (X := X) π T) (samplerRelJB π S) =
      samplerRelJB π {γ | ∃ κ ∈ S, ∃ ι ∈ T, γ = κ ∘ ι} := by
  ext ⟨rf, rc⟩
  constructor
  · rintro ⟨rm, ⟨κ, hκS, hA⟩, ⟨ι, hιT, hB⟩⟩
    exact ⟨κ ∘ ι, ⟨κ, hκS, ι, hιT, rfl⟩,
      fun q k => (hB q k).trans (hA q (ι k))⟩
  · rintro ⟨γ, ⟨κ, hκS, ι, hιT, rfl⟩, h⟩
    exact ⟨fun q j => rf q (κ j), ⟨κ, hκS, fun q j => rfl⟩,
      ⟨ι, hιT, fun q k => h q k⟩⟩

/-- The bundled relation refines the per-port-independent one: a shared
selection is in particular a per-port selection. -/
theorem samplerRelJB_subset_perPort {π : Type*} (S : Set (Fin n → Fin m))
    (p : (π → Fin m → X) × (π → Fin n → X))
    (hp : p ∈ samplerRelJB π S) (q : π) :
    (p.1 q, p.2 q) ∈ samplerRelJ (X := X) S := by
  obtain ⟨ι, hι, h⟩ := hp
  exact ⟨ι, hι, fun k => h q k⟩

/-- The bundled and per-port-independent semantics genuinely differ: with two
ports and two admissible index maps, choosing different maps at the two ports
is per-port admissible but not bundled-admissible. -/
theorem perPort_ne_bundled :
    ∃ p : (Bool → Fin 2 → Fin 2) × (Bool → Fin 1 → Fin 2),
      (∀ q, (p.1 q, p.2 q) ∈
        samplerRelJ (X := Fin 2)
          {ι | ι = (fun _ => 0) ∨ ι = (fun _ => 1)}) ∧
      p ∉ samplerRelJB (X := Fin 2) Bool
          {ι | ι = (fun _ => 0) ∨ ι = (fun _ => 1)} := by
  refine ⟨⟨fun _ k => k, fun q _ => cond q 1 0⟩, ?_, ?_⟩
  · intro q
    cases q
    · exact ⟨fun _ => 0, Or.inl rfl, fun _ => rfl⟩
    · exact ⟨fun _ => 1, Or.inr rfl, fun _ => rfl⟩
  · rintro ⟨ι, -, h⟩
    have h0 : (0 : Fin 2) = ι 0 := h false 0
    have h1 : (1 : Fin 2) = ι 0 := h true 0
    exact absurd (h1.trans h0.symm) (by decide)

end Sampler

end DoubleCat.CrossSite
