import SuFunctor.StateSpace.FamCoproducts
import SuFunctor.StateSpace.FamLimits
import SuFunctor.StateSpace.CountableCoproducts
import SuFunctor.StateSpace.Adjudication

/-! # The completed ω-semialgebraic category, and the bag space

Instantiation of the free countable coproduct completion at the category
of ω-semialgebraic spaces.  `FamObj OmegaSA` is the enlarged state-space
category:

* it keeps the whole finite-limit census (componentwise);
* it has **all** countable coproducts — in particular of families whose
  ambient dimensions grow unboundedly, the case the concrete tagged
  unions of `StateSpace/CountableCoproducts.lean` provably cannot host;
* the coproducts are disjoint and universal, the initial object is
  strict, and the category is still not balanced (the cubing witness
  transports along the singleton embedding);
* the exact-ℚ data story survives: one countable *dimension-tagged*
  carving alphabet `(n : ℕ) × List (PolyCond n)` covers all ambient
  dimensions at once, so a family presentation is a countable stream of
  finite rational words (`countable_famPieceAlphabet`).

The acceptance object is the **bag space** `∐ₙ Symⁿ(ℝ)`: each symmetric
power `Symⁿ(ℝ) = ℝⁿ/Sₙ` is realized as its sorted cone — a *single*
basic rational piece `x₀ ≤ x₁ ≤ ⋯` (`sortedCone`, with
`mem_sortedCone_iff_monotone` as the semantic receipt; the sorting map
is the standard homeomorphism `Symⁿ(ℝ) ≅ {x monotone}`) — and the bag is
the countable family `bagObj` of all the cones, which **is** the
coproduct of its sectors (`bagIsColimit`).  Sector dimensions grow with
`n`; the family hosts them anyway.  Copairing out of the bag
(`bagDesc`) is the "assembles into one function on the bag space" step
of the plated-hypernet denotation discipline.  Componentwise the
sectors are basic, hence locally closed, so the realization
(`famSpace`) is a locally compact second-countable Hausdorff space —
the interface the record tier consumes — via the countable-disjoint-sum
instances (`famSpace_locallyCompactSpace`).

The comparison with the concrete tagged unions: for a common-ambient
family, the copairing of the embedded injections gives a canonical
morphism `famCmp` from the free coproduct to the embedded tagged union.
It induces a bijection on morphisms into every singleton family
(`famCmpHomEquiv`) — the two coproducts agree against the old world —
but it is **never** an isomorphism (`famCmp_not_isIso`): the completion
remembers sector structure.  Likewise the embedding does not send the
empty object to the initial family (`ySing_emptyObj_not_initial`).
-/

namespace SuFunctor.StateSpace

open MvPolynomial Set CategoryTheory CategoryTheory.Limits FamObj

noncomputable section

/-! ## The completed category and its census instances -/

/-- The completed state-space category: countable families of
ω-semialgebraic spaces. -/
abbrev FamOmegaSA : Type 1 := FamObj OmegaSA

example : HasFiniteLimits FamOmegaSA := inferInstance
example : HasCountableCoproducts FamOmegaSA := inferInstance
example : HasStrictInitialObjects FamOmegaSA := inferInstance

/-- **The completion is not balanced**: the cubing witness transports
along the singleton embedding (which preserves monos and epis and
reflects isomorphisms). -/
theorem famOmegaSA_not_balanced :
    ∃ (A B : FamOmegaSA) (f : A ⟶ B), Mono f ∧ Epi f ∧ ¬ IsIso f := by
  refine ⟨ySing realObj, ySing realObj, ySingMap cubeHom, ?_, ?_, ?_⟩
  · haveI := mono_cubeHom
    exact ySingMap_mono cubeHom
  · haveI := epi_cubeHom
    exact ySingMap_epi cubeHom
  · intro h
    haveI := h
    exact not_isIso_cubeHom (ySingMap_isIso cubeHom)

/-- The singleton embedding does not preserve the initial object: the
one-sector family over the empty space is not initial (the completion's
initial object is the empty family). -/
theorem ySing_emptyObj_not_initial :
    ¬ Nonempty (IsInitial (ySing emptyObj)) :=
  ySing_not_initial emptyObj ⟨Bool, fun _ => unitObj⟩
    false true (by decide) default default

/-! ## The exact fragment: one dimension-tagged alphabet -/

/-- The dimension-tagged carving alphabet is countable: a single
countable alphabet of pieces covers every ambient dimension at once, so
a countable family of ω-semialgebraic presentations is a countable
stream of finite rational words.  (This is the theorem that dies if the
coefficient pin is widened to `ℝ` — at the per-dimension alphabet, one
sigma-component upstream.) -/
theorem countable_famPieceAlphabet :
    Countable ((n : ℕ) × List (PolyCond n)) :=
  inferInstance

/-! ## The bag space `∐ₙ Symⁿ(ℝ)` -/

/-- The sorted-cone carving in dimension `n`: the adjacent inequalities
`xᵢ ≤ xᵢ₊₁`, one degree-1 rational condition per adjacent pair. -/
def sortedConds (n : ℕ) : List (PolyCond n) :=
  (List.range n).filterMap fun i =>
    if h : i + 1 < n then
      some ⟨X ⟨i, Nat.lt_of_succ_lt h⟩ - X ⟨i + 1, h⟩, .le⟩
    else none

lemma mem_basicSet_sortedConds {n : ℕ} (x : Fin n → ℝ) :
    x ∈ BasicSet (sortedConds n) ↔
      ∀ (i : ℕ) (h : i + 1 < n), x ⟨i, Nat.lt_of_succ_lt h⟩ ≤ x ⟨i + 1, h⟩ := by
  constructor
  · intro hx i h
    have hc : (⟨X ⟨i, Nat.lt_of_succ_lt h⟩ - X ⟨i + 1, h⟩, .le⟩ : PolyCond n) ∈
        sortedConds n := by
      refine List.mem_filterMap.mpr ⟨i, List.mem_range.mpr (Nat.lt_of_succ_lt h), ?_⟩
      rw [dif_pos h]
    have := hx _ hc
    rw [PolyCond.holds_le] at this
    simpa [sub_nonpos] using this
  · intro hx c hc
    obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp hc
    by_cases h : i + 1 < n
    · rw [dif_pos h] at hi
      obtain rfl := Option.some.inj hi
      rw [PolyCond.holds_le]
      simpa [sub_nonpos] using hx i h
    · rw [dif_neg h] at hi
      simp at hi

/-- The sorted cone is exactly the monotone tuples. -/
theorem mem_sortedCone_iff_monotone {n : ℕ} (x : Fin n → ℝ) :
    x ∈ BasicSet (sortedConds n) ↔ Monotone x := by
  rw [mem_basicSet_sortedConds]
  constructor
  · intro hadj
    have key : ∀ (k : ℕ) (a : Fin n) (hk : a.1 + k < n), x a ≤ x ⟨a.1 + k, hk⟩ := by
      intro k
      induction k with
      | zero =>
          intro a hk
          exact le_of_eq (congrArg x (Fin.ext rfl))
      | succ k ih =>
          intro a hk
          have h1 : a.1 + k < n := by omega
          have h2 : (a.1 + k) + 1 < n := by omega
          calc x a ≤ x ⟨a.1 + k, h1⟩ := ih a h1
            _ ≤ x ⟨a.1 + k + 1, h2⟩ := hadj (a.1 + k) h2
            _ = x ⟨a.1 + (k + 1), hk⟩ := congrArg x (Fin.ext
                  (show a.1 + k + 1 = a.1 + (k + 1) by omega))
    intro a b hab
    have hk : a.1 + (b.1 - a.1) < n := by omega
    calc x a ≤ x ⟨a.1 + (b.1 - a.1), hk⟩ := key _ a hk
      _ = x b := congrArg x (Fin.ext
          (show a.1 + (b.1 - a.1) = b.1 by
            have h := (Fin.le_def.mp hab)
            omega))
  · intro hmono i h
    exact hmono (by simp [Fin.mk_le_mk])

/-- The `n`-th bag sector: `Symⁿ(ℝ)` realized as the sorted cone in
`ℝⁿ` — a single basic rational piece.  (The sorting map is the standard
homeomorphism `Symⁿ(ℝ) = ℝⁿ/Sₙ ≅ {x : x monotone}`; the categorical
object is the cone.) -/
def sortedCone (n : ℕ) : OmegaSA :=
  ⟨n, BasicSet (sortedConds n), IsOmegaSA.of_basic _⟩

/-- Each bag sector is a citizen: basic pieces are locally closed. -/
theorem sortedCone_isLocallyClosed (n : ℕ) :
    IsLocallyClosed (sortedCone n).carrier :=
  isLocallyClosed_basicSet _

/-- **The bag space** `∐ₙ Symⁿ(ℝ)`: the countable family of all the
sorted cones — sector dimension grows with `n`, which is exactly what
no concrete common-ambient tagged union can host, and what the
completion hosts by construction. -/
@[reducible]
def bagObj : FamOmegaSA :=
  ⟨ℕ, fun n => sortedCone n⟩

/-- The bag's sector injections. -/
def bagInj (n : ℕ) : ySing (sortedCone n) ⟶ bagObj :=
  famComponentInj bagObj n

/-- **The acceptance theorem**: the bag space is a first-class object of
the completed category, and it *is* the countable coproduct of its
symmetric-power sectors. -/
def bagIsColimit :
    IsColimit (famComponentsCofan bagObj) :=
  famComponentsIsColimit bagObj

/-- Copairing out of the bag: a family of sector denotations assembles
into one morphism on the bag space — the descent step of the
plated-hypernet denotation discipline ("outputs carrying no plate axis
factor through the symmetric quotient and assemble on the bag"). -/
def bagDesc {T : FamOmegaSA} (legs : ∀ n, ySing (sortedCone n) ⟶ T) :
    bagObj ⟶ T :=
  (famComponentsIsColimit bagObj).desc (Cofan.mk T legs)

/-! ## Realization: the completion's citizens are lcsc one level up -/

/-- The realization of a family: the disjoint sum of its components'
carriers. -/
def famSpace (A : FamOmegaSA) : Type :=
  (i : A.ι) × (A.X i : Type)

instance (A : FamOmegaSA) : TopologicalSpace (famSpace A) :=
  inferInstanceAs (TopologicalSpace ((i : A.ι) × (A.X i : Type)))

instance (A : FamOmegaSA) : T2Space (famSpace A) :=
  inferInstanceAs (T2Space ((i : A.ι) × (A.X i : Type)))

instance (A : FamOmegaSA) : SecondCountableTopology (famSpace A) :=
  inferInstanceAs (SecondCountableTopology ((i : A.ι) × (A.X i : Type)))

/-- A countable disjoint sum of locally compact spaces is locally
compact.  (Componentwise neighborhoods: `Sigma.mk` is an open
embedding.) -/
theorem sigma_locallyCompactSpace {ι : Type} {π : ι → Type}
    [∀ i, TopologicalSpace (π i)] [∀ i, LocallyCompactSpace (π i)] :
    LocallyCompactSpace ((i : ι) × π i) := by
  constructor
  rintro ⟨i, x⟩ n hn
  rw [Sigma.nhds_mk] at hn
  obtain ⟨k, hk_mem, hk_sub, hk_cpt⟩ :=
    LocallyCompactSpace.local_compact_nhds x _ (Filter.mem_map.mp hn)
  refine ⟨Sigma.mk i '' k, ?_, ?_, hk_cpt.image continuous_sigmaMk⟩
  · rw [Sigma.nhds_mk]
    exact Filter.image_mem_map hk_mem
  · exact Set.image_subset_iff.mpr hk_sub

/-- **Citizenship one level up**: a family of locally closed
ω-semialgebraic spaces realizes to a locally compact (second-countable,
Hausdorff) space — the state-space interface of the record tier, for
objects the concrete category cannot host. -/
theorem famSpace_locallyCompactSpace (A : FamOmegaSA)
    (h : ∀ i, IsLocallyClosed (A.X i).carrier) :
    LocallyCompactSpace (famSpace A) := by
  haveI : ∀ i, LocallyCompactSpace (A.X i : Type) :=
    fun i => (h i).locallyCompactSpace
  exact sigma_locallyCompactSpace

/-- The bag space's lcsc receipt. -/
theorem bagSpace_locallyCompactSpace : LocallyCompactSpace (famSpace bagObj) :=
  famSpace_locallyCompactSpace bagObj fun n => sortedCone_isLocallyClosed n

/-! ## Comparison with the concrete tagged unions -/

section Comparison

variable {n : ℕ} (K : ℕ → Set (Fin n → ℝ)) (hK : ∀ i, IsOmegaSA (K i))

/-- The comparison morphism: from the free coproduct of the embedded
summands to the embedded concrete tagged union — the copairing of the
embedded injections. -/
def famCmp : famSigma (fun i => ySing (summand K hK i)) ⟶
    ySing (coprodObj K hK) :=
  famSigmaDesc _ fun i => ySingMap (coprodInj K hK i)

/-- Against the old world the two coproducts agree: precomposition with
the comparison is a bijection on morphisms into every singleton family
(both objects copair the same data). -/
def famCmpHomEquiv (T : OmegaSA) :
    (ySing (coprodObj K hK) ⟶ ySing T) ≃
      (famSigma (fun i => ySing (summand K hK i)) ⟶ ySing T) where
  toFun g := famCmp K hK ≫ g
  invFun h := ySingMap ((coprodIsColimit K hK).desc
    (Cofan.mk T fun i =>
      (famSigmaInj (fun i' => ySing (summand K hK i')) i ≫ h).app PUnit.unit))
  left_inv g := by
    have hlegs : ∀ (j : Discrete ℕ),
        (coprodCofan K hK).ι.app j ≫ g.app PUnit.unit =
        (Cofan.mk T fun i =>
          (famSigmaInj (fun i' => ySing (summand K hK i')) i ≫
            (famCmp K hK ≫ g)).app PUnit.unit).ι.app j := by
      rintro ⟨i⟩
      exact (Category.id_comp _).symm
    have huniq := (coprodIsColimit K hK).uniq
      (Cofan.mk T fun i =>
        (famSigmaInj (fun i' => ySing (summand K hK i')) i ≫
          (famCmp K hK ≫ g)).app PUnit.unit)
      (g.app PUnit.unit) hlegs
    refine FamObj.Hom.ext' (funext fun _ => rfl) (fun u => ?_)
    exact (congrArg (fun k => k ≫ eqToHom _) huniq.symm).trans
      (Category.comp_id _)
  right_inv h := by
    have hfac := (coprodIsColimit K hK).fac
      (Cofan.mk T fun i' =>
        (famSigmaInj (fun i'' => ySing (summand K hK i'')) i' ≫ h).app
          PUnit.unit)
    refine FamObj.Hom.ext' (funext fun p => rfl) (fun p => ?_)
    exact (congrArg (fun k => k ≫ eqToHom _) (hfac ⟨p.1⟩)).trans
      ((congrArg (fun k => k ≫ eqToHom _) (Category.id_comp _)).trans
        (Category.comp_id _))

/-- But the comparison is **never** an isomorphism — even for all-empty
families: an isomorphism of families has a bijective reindexing, and the
free coproduct has `ℕ`-many sectors where the embedded tagged union has
one.  The completion remembers sector structure; the two objects are
identified only by the realization, not in the category. -/
theorem famCmp_not_isIso : ¬ IsIso (famCmp K hK) := by
  intro h
  haveI := h
  have hbij := famIsIso_reindex_bijective (famCmp K hK)
  have h01 : (⟨0, PUnit.unit⟩ : (i : ℕ) × PUnit) = ⟨1, PUnit.unit⟩ :=
    hbij.1 (Subsingleton.elim _ _)
  have : (0 : ℕ) = 1 := congrArg Sigma.fst h01
  exact absurd this (by omega)

end Comparison

end

end SuFunctor.StateSpace
