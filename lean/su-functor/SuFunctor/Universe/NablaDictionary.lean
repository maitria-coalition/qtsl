import SuFunctor.Universe.LocallyClosedLayer

/-! # The ∇-normal-form bridge: coupled DNFs are Moss disjunctions

The dictionary lemma offered back to the locally-closed layer, giving
its constructible stratum its coalgebraic-logic name (rung I of the
temporal-sheaf-carrier design).

Moss's cover modality on a hyperspace reads, semantically,
`∇ A = □ (⋃ i, A i) ∧ ⋀ i, ◇ (A i)`: the citizen is contained in the
family's union and meets every member (Venema–Vickers–Vosmaer's
presentation of the Vietoris powerlocale has exactly these as its
basic opens).  On the nonempty-compact stratum this file records:

* the two Moss translations, `□ a = ∇ {a}` (`boxClass_eq_nablaClass`)
  and `◇ a = ∇ {a, ⊤}` (`diaClass_eq_nablaClass`) — the first
  *unconditionally*, because `∇` of the empty family is the **empty**
  class here (`nablaClass_of_isEmpty`): the classical translation's
  second disjunct `∇ ∅` is the empty-citizen clause, and the empty
  citizen is unrepresentable in `NonemptyCompacts`;
* the polarity restatement of the spec-atom class
  (`crescentClass_eq_box_inter_dia`, definitional): the crescent was
  hit-and-miss all along — one `□` of the safety body, finitely many
  `◇`s of the escape regions;
* **the dictionary** (`crescentClass_eq_nablaClass`): a spec atom's
  class is a *single ∇-basic*, whose family is the safety body
  together with the escape regions **relativized to it** — the
  ∇-arguments are (relatively) open subsets of the safety body's own
  subspace, i.e. the atom's `∇` is computed over the safety body, not
  the ambient carrier;
* **the headline** (`dnfClass_eq_iUnion_nablaClass`): the class of a
  coupled DNF is a finite disjunction of ∇-basics — the coupled DNF
  is coalgebraic modal logic's own disjunctive normal form, and
  `IsConstructibleUnion` is its topological shadow.  The definability
  guard "definable ⟹ locally closed, never conversely" thereby
  becomes a *syntax* statement: the judgment-definable classes are
  exactly the finitely ∇-presented ones
  (`exists_nabla_presentation_of_finite` produces the presentation
  for arbitrary finite demand sets);
* the two preregistered refuting fixtures: the relativization is
  load-bearing (`bare_escape_dictionary_false` — the ambient-escape
  family classifies strictly more citizens), and so is the container
  component (`nablaClass_of_isEmpty` +
  `containerless_dictionary_false` — without it the `k = 0` instance
  collapses to the empty class).

Nothing here is topological: the dictionary is set algebra, and the
topological content (local closedness, constructibility) is already
landed in `LocallyClosedLayer` / `VietorisStratum`.
-/

namespace SuFunctor.Universe

open scoped ENNReal
open TopologicalSpace

/-! ## Moss's cover modality, semantically, on nonempty compacts -/

section Nabla

variable {X : Type*} [TopologicalSpace X]

/-- The box class of a region: citizens contained in it (the safety
polarity — `Miss` of the complement). -/
def boxClass (S : Set X) : Set (NonemptyCompacts X) :=
  {K | (K : Set X) ⊆ S}

/-- The diamond class of a region: citizens meeting it (the liveness
polarity — `Hit`). -/
def diaClass (S : Set X) : Set (NonemptyCompacts X) :=
  {K | ((K : Set X) ∩ S).Nonempty}

/-- Moss's cover modality, read semantically on the hyperspace:
contained in the union, meeting every member. -/
def nablaClass {ι : Sort*} (A : ι → Set X) : Set (NonemptyCompacts X) :=
  boxClass (⋃ i, A i) ∩ ⋂ i, diaClass (A i)

theorem mem_nablaClass_iff {ι : Sort*} {A : ι → Set X}
    {K : NonemptyCompacts X} :
    K ∈ nablaClass A
      ↔ (K : Set X) ⊆ (⋃ i, A i) ∧ ∀ i, ((K : Set X) ∩ A i).Nonempty := by
  simp only [nablaClass, Set.mem_inter_iff, Set.mem_iInter, boxClass,
    diaClass, Set.mem_setOf_eq]

/-- `∇` of the empty family is the **empty** class on nonempty
compacts: the box face demands containment in `∅`.  (On the full
closed-sets hyperspace this class would instead be the singleton of
the empty citizen; that citizen's absence here is what frees the `□`
translation below from its `∇ ∅` disjunct.) -/
theorem nablaClass_of_isEmpty {ι : Sort*} [IsEmpty ι] (A : ι → Set X) :
    nablaClass A = ∅ := by
  ext K
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hK
  obtain ⟨x, hx⟩ := K.nonempty
  have hmem := (mem_nablaClass_iff.mp hK).1 hx
  rw [Set.iUnion_of_empty] at hmem
  exact hmem

/-- Moss translation, box: `□ a = ∇ {a}` on nonempty compacts — with
no `∇ ∅` disjunct, per `nablaClass_of_isEmpty`. -/
theorem boxClass_eq_nablaClass (S : Set X) :
    boxClass S = nablaClass fun _ : Unit => S := by
  ext K
  rw [mem_nablaClass_iff]
  constructor
  · intro hK
    refine ⟨by rwa [Set.iUnion_const], fun _ => ?_⟩
    obtain ⟨x, hx⟩ := K.nonempty
    exact ⟨x, hx, hK hx⟩
  · rintro ⟨hbox, -⟩
    rwa [Set.iUnion_const] at hbox

/-- Moss translation, diamond: `◇ a = ∇ {a, ⊤}` on nonempty
compacts. -/
theorem diaClass_eq_nablaClass (S : Set X) :
    diaClass S = nablaClass fun b : Bool => if b then S else Set.univ := by
  ext K
  rw [mem_nablaClass_iff]
  constructor
  · intro hK
    refine ⟨fun x _ => Set.mem_iUnion.mpr ⟨false, by simp⟩, fun b => ?_⟩
    cases b
    · simpa using K.nonempty
    · simpa [diaClass] using hK
  · rintro ⟨-, hdia⟩
    simpa [diaClass] using hdia true

end Nabla

/-! ## The spec-atom dictionary -/

variable {V : Type*} [Fintype V]

/-- The polarity restatement, definitional: the crescent was
hit-and-miss all along — `□` of the safety body, `◇` of each escape
region. -/
theorem crescentClass_eq_box_inter_dia (u : ProbPenalty V)
    (𝒱 : Set (ProbPenalty V)) :
    crescentClass u 𝒱
      = boxClass (compile u) ∩ ⋂ v ∈ 𝒱, diaClass ((compile v)ᶜ) := rfl

/-- The ∇-family of a spec atom: the safety body, together with each
escape region **relativized to it**.  The arguments are (relatively)
open subsets of the safety body's own subspace — the atom's `∇` is
computed over the safety body, not the ambient carrier.  The
preregistered mutants certify both components: dropping the
relativization admits extra citizens (`bare_escape_dictionary_false`),
and dropping the container empties the `k = 0` instance
(`containerless_dictionary_false`). -/
def crescentFam (u : ProbPenalty V) {k : ℕ} (v : Fin k → ProbPenalty V) :
    Option (Fin k) → Set (BelState V)
  | none => compile u
  | some i => (compile (v i))ᶜ ∩ compile u

/-- **The dictionary**: a spec atom's class is a single ∇-basic — one
`□`-generator (the safety body, the family's union) conjoined with
finitely many `◇`-generators (the relativized escapes, plus the
body itself, whose `◇` is vacuous for nonempty citizens). -/
theorem crescentClass_eq_nablaClass (u : ProbPenalty V) {k : ℕ}
    (v : Fin k → ProbPenalty V) :
    crescentClass u (Set.range v) = nablaClass (crescentFam u v) := by
  ext K
  rw [mem_crescentClass_iff, mem_nablaClass_iff]
  constructor
  · rintro ⟨hsub, hesc⟩
    refine ⟨fun x hx => Set.mem_iUnion.mpr ⟨none, hsub hx⟩, ?_⟩
    rintro (_ | i)
    · obtain ⟨x, hx⟩ := K.nonempty
      exact ⟨x, hx, hsub hx⟩
    · obtain ⟨x, hxK, hxv⟩ := hesc (v i) ⟨i, rfl⟩
      exact ⟨x, hxK, hxv, hsub hxK⟩
  · rintro ⟨hbox, hdia⟩
    have hsub : (K : Set (BelState V)) ⊆ compile u := by
      intro x hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hbox hx)
      exact match j, hj with
        | none, hj => hj
        | some _, hj => hj.2
    refine ⟨hsub, ?_⟩
    rintro w ⟨i, rfl⟩
    obtain ⟨x, hxK, hxvi, -⟩ := hdia (some i)
    exact ⟨x, hxK, hxvi⟩

/-- **The headline: coupled DNFs are ∇-disjunctions.**  The class of a
coupled DNF is a finite union of ∇-basics — coalgebraic modal logic's
own disjunctive normal form.  Composed with
`isConstructibleUnion_dnfClass`, this is the syntax form of the
definability guard: judgment-definable ⟹ finitely ∇-presented ⟹
constructible, with the first arrow an identity. -/
theorem dnfClass_eq_iUnion_nablaClass {n : ℕ} (u : Fin n → ProbPenalty V)
    {k : Fin n → ℕ} (v : ∀ i, Fin (k i) → ProbPenalty V) :
    dnfClass u (fun i => Set.range (v i))
      = ⋃ i, nablaClass (crescentFam (u i) (v i)) :=
  Set.iUnion_congr fun i => crescentClass_eq_nablaClass (u i) (v i)

/-- Every judgment-definable class is finitely ∇-presented: for
arbitrary finite demand sets, some enumeration exhibits the DNF class
as a finite disjunction of ∇-basics. -/
theorem exists_nabla_presentation_of_finite {n : ℕ}
    (u : Fin n → ProbPenalty V) (𝒱 : Fin n → Set (ProbPenalty V))
    (h𝒱 : ∀ i, (𝒱 i).Finite) :
    ∃ (k : Fin n → ℕ) (v : ∀ i, Fin (k i) → ProbPenalty V),
      (∀ i, Set.range (v i) = 𝒱 i)
        ∧ dnfClass u 𝒱 = ⋃ i, nablaClass (crescentFam (u i) (v i)) := by
  choose k v hv using fun i => (h𝒱 i).fin_embedding
  refine ⟨k, fun i => ⇑(v i), fun i => hv i, ?_⟩
  have h𝒱' : 𝒱 = fun i => Set.range ⇑(v i) := funext fun i => (hv i).symm
  rw [h𝒱']
  exact dnfClass_eq_iUnion_nablaClass u fun i => ⇑(v i)

/-! ## The preregistered refutations -/

/-- The point mass escapes the top body: `compile ⊤` grades every ray
to length `0`. -/
theorem dirac_notMem_compile_top :
    BelState.dirac (0 : Fin 1) ∉ compile (⊤ : ProbPenalty (Fin 1)) := by
  rintro ⟨μ, γ, h0, hle, he⟩
  rw [Pi.top_apply, grade_top] at hle
  rw [le_antisymm hle h0, zero_smul] at he
  simpa using congrFun he 0

/-- **The relativization is load-bearing** (preregistered mutant m2):
the bare-escape family — container plus *ambient* escapes — is not a
dictionary for the crescent.  Witness: at `u = v = ⊤`, the two-point
citizen `{0, dirac 0}` is contained in `compile ⊤ ∪ (compile ⊤)ᶜ`
(every citizen is), meets the container at `0` and the ambient escape
at the point mass — yet it is not contained in the safety body, so it
lies in no crescent. -/
theorem bare_escape_dictionary_false :
    crescentClass (⊤ : ProbPenalty (Fin 1))
        (Set.range fun _ : Fin 1 => (⊤ : ProbPenalty (Fin 1)))
      ≠ nablaClass (fun j : Option (Fin 1) =>
          j.elim (compile (⊤ : ProbPenalty (Fin 1)))
            fun _ => (compile (⊤ : ProbPenalty (Fin 1)))ᶜ) := by
  intro h
  set z := BelState.zero (Fin 1) with hz
  set d := BelState.dirac (0 : Fin 1) with hd
  set K : NonemptyCompacts (BelState (Fin 1)) :=
    ⟨⟨{z, d}, ((Set.finite_singleton d).insert z).isCompact⟩,
      ⟨z, Set.mem_insert z {d}⟩⟩ with hK
  have hKnabla : K ∈ nablaClass (fun j : Option (Fin 1) =>
      j.elim (compile (⊤ : ProbPenalty (Fin 1)))
        fun _ => (compile (⊤ : ProbPenalty (Fin 1)))ᶜ) := by
    rw [mem_nablaClass_iff]
    constructor
    · intro x _
      by_cases hxc : x ∈ compile (⊤ : ProbPenalty (Fin 1))
      · exact Set.mem_iUnion.mpr ⟨none, hxc⟩
      · exact Set.mem_iUnion.mpr ⟨some 0, hxc⟩
    · rintro (_ | i)
      · exact ⟨z, Set.mem_insert z {d}, zero_mem_compile _⟩
      · exact ⟨d, Set.mem_insert_of_mem z rfl, dirac_notMem_compile_top⟩
  have hKcres : K ∈ crescentClass (⊤ : ProbPenalty (Fin 1))
      (Set.range fun _ : Fin 1 => (⊤ : ProbPenalty (Fin 1))) := by
    rw [h]; exact hKnabla
  exact dirac_notMem_compile_top
    ((mem_crescentClass_iff.mp hKcres).1 (Set.mem_insert_of_mem z rfl))

/-- **The container is load-bearing** (preregistered fixture w4): with
the container component deleted, the `k = 0` dictionary instance is
false — the demand-free crescent of the zero penalty owns the zero
citizen, while `∇` of the empty family owns nothing
(`nablaClass_of_isEmpty`). -/
theorem containerless_dictionary_false :
    crescentClass (0 : ProbPenalty (Fin 1))
        (Set.range (Fin.elim0 : Fin 0 → ProbPenalty (Fin 1)))
      ≠ nablaClass (fun i : Fin 0 =>
          (compile (Fin.elim0 i))ᶜ ∩ compile (0 : ProbPenalty (Fin 1))) := by
  intro h
  have hmem : (⟨⟨{BelState.zero (Fin 1)}, isCompact_singleton⟩,
      ⟨BelState.zero (Fin 1), rfl⟩⟩ : NonemptyCompacts (BelState (Fin 1)))
      ∈ crescentClass (0 : ProbPenalty (Fin 1)) (Set.range Fin.elim0) := by
    rw [mem_crescentClass_iff]
    refine ⟨?_, ?_⟩
    · rintro x rfl
      exact zero_mem_compile _
    · rintro w ⟨i, -⟩
      exact i.elim0
  rw [h, nablaClass_of_isEmpty] at hmem
  exact absurd hmem (Set.notMem_empty _)

end SuFunctor.Universe
