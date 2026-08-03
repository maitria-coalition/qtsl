import SuFunctor.Universe.LocallyClosedLayer
import SuFunctor.Universe.SpecDnf

/-! # The pair-sequent calculus of the spec stratum

The two sequent species of the coupled judgment, as an actual proof
system: **satisfaction sequents** (a system against a finite
disjunction of spec atoms — the system boundary) and **entailment
sequents** (spec against spec), with the introduction rules the layer's
completeness analysis identified — matching, splitting, and the
blocking criterion — plus the two structural rules disjunction needs.
Every rule's soundness is proved against the coupled judgment, and the
blocking rule's *completeness* (`coupled_union_refinement_iff`) is
inherited by the calculus, which is what makes the admissible rules
theorems rather than postulates.

Headline facts, each with its proof below:

* **One soundness engine.**  All three introduction rules route through
  the blocking criterion: the matching and splitting side conditions
  each imply that every valid selection is blocked (`matching_blocked`,
  `splitting_blocked`) — the extremal-face analysis of the layer,
  mechanized at the rule level.  Soundness of the calculus
  (`EntDeriv.sound`, `SatDeriv.sound`) is then a single induction whose
  introduction cases all discharge against
  `coupled_union_refinement_iff`, instantiated at the unrestricted
  system class — so derivability is sound over *every* class of
  systems, citizens included, with no containment side conditions.
* **Completeness, and cut for free.**  A semantically valid entailment
  is derivable by one `split` and per-disjunct `blocking`
  (`entDeriv_of_famClass_subset`; the class-parametric form is
  `entDeriv_of_valid`).  Consequently **cut is admissible with no side
  hypotheses** (`EntDeriv.cut`): compose the two soundness facts and
  re-derive — admissibility inherited from completeness, not proved by
  permutation.  Reflexivity is likewise derived (`EntDeriv.refl`), via
  identity matching.
* **Zero ex-falso rules, both directions theorems.**  The constructor
  list contains no ex-falso rule; both classical directions are derived
  facts of the same judgment, pointing opposite ways across the two
  species.  Entailment side: an unsatisfiable premise entails every
  conclusion (`EntDeriv.of_not_con`) — some demand sits at or below the
  floor, and that demand blocks every selection, so the blocking rule
  alone suffices.  Satisfaction side: the inconsistent system derives
  nothing (`not_satDeriv_top`) — with no side condition on the
  conclusion family, because under the option-A shape of `SpecAtom`
  every liveness slot is inhabited.
* **The properness presupposition is a theorem of the calculus.**
  Every derivable satisfaction sequent's system is proper
  (`SatDeriv.proper`): to satisfy anything, first exist.  The
  mechanism: any dip already witnesses properness (`Dip.proper`,
  `Dip.dip_top` — strictly below a mark somewhere is strictly below
  `⊤` there), and every atom's liveness slot contains the properness
  demand by construction (`SpecAtom.top_mem`).  Two corollaries pin
  the option-A reading exactly: the safety-only atom `(u, {⊤})` is
  satisfied precisely by the safe *and proper* systems
  (`SpecAtom.coupledSat_safetyOnly_iff`), and adjoining the properness
  demand to an atom changes no verdict once any demand is present
  (`coupledSat_insert_top_iff`,
  `coupledSat_insert_top_of_nonempty`) — the properness row of a
  satisfaction certificate is subsumed by any other dip-witness row.
* **The option-A properness demand pays its way inside the calculus.**
  In `splitting_blocked`, selections that pick a `⊤` mark are blocked
  by the premise's *own* properness demand — the structural `top_mem`
  is load-bearing in the completeness bookkeeping, not decoration.
* **Sequent sides are the landed presentations.**  The calculus
  quantifies over `Fin`-indexed atom families; `SpecDnf.ofFam` and
  `SpecDnf.exists_ofFam_eq` identify these with the presentation type
  `SpecDnf`, class-for-class (`SpecDnf.ofFam_modelClass`), and a
  derivable satisfaction sequent places the citizen's body in the
  spec's constructible hyperspace class (`SatDeriv.compileNC_mem`).
-/

namespace SuFunctor.Universe

open scoped ENNReal

universe u

variable {K : Type u}

/-! ## Dips witness properness

Strictly below a mark somewhere is strictly below `⊤` there: the
∃-face of the coupled judgment carries an existence assertion in every
dip, which is why the properness demand costs nothing once any demand
is present. -/

/-- Any dip already witnesses properness: at the dip point the system
is strictly below the mark, hence finite. -/
theorem Dip.proper {σ v : K → ℝ≥0∞} (h : Dip σ v) : ∃ μ, σ μ ≠ ⊤ := by
  obtain ⟨μ, hμ⟩ := h
  exact ⟨μ, (lt_of_lt_of_le hμ le_top).ne⟩

/-- Any dip yields a dip under the properness demand. -/
theorem Dip.dip_top {σ v : K → ℝ≥0∞} (h : Dip σ v) : Dip σ ⊤ :=
  h.mono_mark le_top

/-- A dip under the properness demand is exactly properness. -/
theorem dip_top_iff_proper {σ : K → ℝ≥0∞} :
    Dip σ ⊤ ↔ ∃ μ, σ μ ≠ ⊤ := by
  constructor
  · rintro ⟨μ, hμ⟩
    rw [Pi.top_apply] at hμ
    exact ⟨μ, hμ.ne⟩
  · rintro ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    rw [Pi.top_apply]
    exact lt_top_iff_ne_top.mpr hμ

/-- **Adjoining the properness demand, exactly**: the atom `(u, insert
⊤ 𝒱)` is satisfied iff `(u, 𝒱)` is satisfied by a proper system.  The
properness conjunct is the whole delta. -/
theorem coupledSat_insert_top_iff {σ u : K → ℝ≥0∞}
    {𝒱 : Set (K → ℝ≥0∞)} :
    CoupledSat σ u (insert ⊤ 𝒱) ↔ CoupledSat σ u 𝒱 ∧ ∃ μ, σ μ ≠ ⊤ := by
  constructor
  · rintro ⟨hsafe, hlive⟩
    exact ⟨⟨hsafe, fun v hv => hlive v (Set.mem_insert_of_mem _ hv)⟩,
      dip_top_iff_proper.mp (hlive ⊤ (Set.mem_insert _ _))⟩
  · rintro ⟨⟨hsafe, hlive⟩, hproper⟩
    refine ⟨hsafe, ?_⟩
    rintro v (rfl | hv)
    · exact dip_top_iff_proper.mpr hproper
    · exact hlive v hv

/-- On an atom with any demand at all, adjoining the properness demand
changes no verdict: the properness row of a satisfaction certificate is
subsumed by any other dip-witness row. -/
theorem coupledSat_insert_top_of_nonempty {σ u : K → ℝ≥0∞}
    {𝒱 : Set (K → ℝ≥0∞)} (h𝒱 : 𝒱.Nonempty) :
    CoupledSat σ u (insert ⊤ 𝒱) ↔ CoupledSat σ u 𝒱 := by
  rw [coupledSat_insert_top_iff]
  refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
  obtain ⟨v, hv⟩ := h𝒱
  exact (h.2 v hv).proper

/-! ## Two atom formers -/

namespace SpecAtom

/-- The safety-only atom: floor `u`, liveness slot exactly the
properness demand.  The minimum an atom can demand — the empty slot is
unrepresentable. -/
def safetyOnly (u : K → ℝ≥0∞) : SpecAtom K where
  floor := u
  marks := {⊤}
  finite_marks := Set.finite_singleton _
  top_mem := Set.mem_singleton _

@[simp] theorem safetyOnly_floor (u : K → ℝ≥0∞) :
    (safetyOnly u).floor = u := rfl

@[simp] theorem safetyOnly_marks (u : K → ℝ≥0∞) :
    (safetyOnly u).marks = {(⊤ : K → ℝ≥0∞)} := rfl

/-- **Safety-only means safe and proper**: the safety-only atom is
satisfied exactly by the systems that dominate the floor *and* realize
some point at finite penalty.  The presupposition reading of a bare
safety spec, as a theorem. -/
theorem coupledSat_safetyOnly_iff {σ u : K → ℝ≥0∞} :
    σ ∈ (safetyOnly u).modelClass ↔ u ≤ σ ∧ ∃ μ, σ μ ≠ ⊤ := by
  rw [mem_modelClass_iff]
  constructor
  · rintro ⟨hsafe, hlive⟩
    exact ⟨hsafe, dip_top_iff_proper.mp (hlive ⊤ (Set.mem_singleton _))⟩
  · rintro ⟨hsafe, hproper⟩
    refine ⟨hsafe, ?_⟩
    rintro v hv
    rw [safetyOnly_marks, Set.mem_singleton_iff] at hv
    subst hv
    exact dip_top_iff_proper.mpr hproper

/-- The single-demand atom: floor `u`, one contentful demand `w`
alongside the structural properness demand. -/
def single (u w : K → ℝ≥0∞) : SpecAtom K where
  floor := u
  marks := {w, ⊤}
  finite_marks := (Set.finite_singleton _).insert _
  top_mem := Set.mem_insert_iff.mpr (Or.inr rfl)

@[simp] theorem single_floor (u w : K → ℝ≥0∞) :
    (single u w).floor = u := rfl

@[simp] theorem single_marks (u w : K → ℝ≥0∞) :
    (single u w).marks = {w, ⊤} := rfl

/-- The single-demand atom's judgment: floor domination plus the one
dip — the properness demand is carried by the dip itself. -/
theorem coupledSat_single_iff {σ u w : K → ℝ≥0∞} :
    σ ∈ (single u w).modelClass ↔ u ≤ σ ∧ Dip σ w := by
  rw [mem_modelClass_iff]
  constructor
  · rintro ⟨hsafe, hlive⟩
    exact ⟨hsafe, hlive w (Set.mem_insert _ _)⟩
  · rintro ⟨hsafe, hdip⟩
    refine ⟨hsafe, ?_⟩
    rintro v (rfl | hv)
    · exact hdip
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact hdip.dip_top

end SpecAtom

/-! ## Finite disjunctions as indexed families

The calculus quantifies over `Fin`-indexed families of atoms; the
bridge to the presentation type `SpecDnf` is exact and closes the loop
at the end of the file. -/

/-- The model class of a finite disjunction of atoms, presented as an
indexed family: the union of the disjuncts' model classes. -/
def famClass {n : ℕ} (Φ : Fin n → SpecAtom K) : Set (K → ℝ≥0∞) :=
  ⋃ i, (Φ i).modelClass

theorem mem_famClass_iff {n : ℕ} {Φ : Fin n → SpecAtom K}
    {σ : K → ℝ≥0∞} :
    σ ∈ famClass Φ ↔ ∃ i, CoupledSat σ (Φ i).floor (Φ i).marks := by
  simp [famClass]

theorem famClass_singleton (a : SpecAtom K) :
    famClass ![a] = a.modelClass := by
  ext σ
  simp [famClass, Matrix.cons_val_fin_one]

/-! ## The extremal faces of blocking

The matching and splitting side conditions each imply that every valid
selection is blocked — so the blocking criterion is the calculus's one
soundness engine, and matching and splitting are its two extremal
faces, at the rule level. -/

/-- **Matching implies blocking**: if some conclusion disjunct sits
below the premise in the compiled refinement order (floor below floor,
demands covered floor-relatively), then every valid selection is
blocked — at the matched disjunct's floor if the selection avoids it,
through the covering if it selects a demand there. -/
theorem matching_blocked {m : ℕ} {a : SpecAtom K}
    {Ψ : Fin m → SpecAtom K} {j : Fin m}
    (hfloor : (Ψ j).floor ≤ a.floor)
    (hcov : ∀ v' ∈ (Ψ j).marks, ∃ v ∈ a.marks, v ≤ a.floor ⊔ v')
    (c : Fin m → Option (K → ℝ≥0∞))
    (hc : SelValid (fun j => (Ψ j).marks) c) :
    Blocked a.floor a.marks (fun j => (Ψ j).floor) c := by
  rcases hcj : c j with _ | w
  · exact Or.inr ⟨j, hcj, hfloor.trans le_selSup_left⟩
  · obtain ⟨v, hv, hvle⟩ := hcov w (hc j w hcj)
    exact Or.inl ⟨v, hv, hvle.trans
      (sup_le le_selSup_left (le_selSup_of_eq_some hcj))⟩

/-- **Splitting implies blocking**: under a shared floor, splitting one
demand into a family whose join (with the floor) dominates it blocks
every valid selection.  Three cases, one per selection shape: an
unselected disjunct blocks at the shared floor; a selection that picks
a `⊤` mark is blocked by the premise's *own* properness demand (the
structural `top_mem` doing work inside the calculus); and the
all-demands selection is blocked by the split demand itself, through
the side condition. -/
theorem splitting_blocked {m : ℕ} {u w : K → ℝ≥0∞}
    {wj : Fin m → K → ℝ≥0∞} (hle : w ≤ u ⊔ ⨆ j, wj j)
    (c : Fin m → Option (K → ℝ≥0∞))
    (hc : SelValid (fun j => (SpecAtom.single u (wj j)).marks) c) :
    Blocked (SpecAtom.single u w).floor (SpecAtom.single u w).marks
      (fun j => (SpecAtom.single u (wj j)).floor) c := by
  by_cases hnone : ∃ j, c j = none
  · obtain ⟨j, hj⟩ := hnone
    exact Or.inr ⟨j, hj, le_selSup_left⟩
  · push Not at hnone
    by_cases htop : ∃ j, c j = some ⊤
    · obtain ⟨j, hj⟩ := htop
      exact Or.inl ⟨⊤, Set.mem_insert_iff.mpr (Or.inr rfl),
        le_selSup_of_eq_some hj⟩
    · push Not at htop
      have hall : ∀ j, c j = some (wj j) := by
        intro j
        rcases hcj : c j with _ | x
        · exact absurd hcj (hnone j)
        · rcases hc j x hcj with rfl | hx
          · rfl
          · rw [Set.mem_singleton_iff] at hx
            subst hx
            exact absurd hcj (htop j)
      exact Or.inl ⟨w, Set.mem_insert _ _, hle.trans
        (sup_le le_selSup_left
          (iSup_le fun j => le_selSup_of_eq_some (hall j)))⟩

/-! ## The entailment species -/

/-- **Entailment sequents**: derivations of spec-to-spec refinement
between finite disjunctions of atoms.  Three introduction rules —
`blocking` (the complete one), `matching`, and `splitting` (the two
extremal compressions a producer may emit instead) — and two
structural rules: `reindex` on the conclusion side (weakening,
permutation, and contraction in one) and `split` on the premise side
(a disjunction entails what each disjunct entails).

Deliberately absent: an axiom rule (derived — `EntDeriv.refl`), a cut
rule (admissible with no side conditions — `EntDeriv.cut`, inherited
from completeness), and any ex-falso rule (derived —
`EntDeriv.of_not_con`: an unsatisfiable premise blocks every selection
through its own liveness slot). -/
inductive EntDeriv {K : Type u} :
    ∀ {n m : ℕ}, (Fin n → SpecAtom K) → (Fin m → SpecAtom K) → Prop where
  /-- The blocking rule: every valid selection against the conclusion
  family is blocked by one domination row.  Complete as well as sound
  (`entDeriv_of_famClass_subset`). -/
  | blocking {m : ℕ} (a : SpecAtom K) (Ψ : Fin m → SpecAtom K)
      (h : ∀ c, SelValid (fun j => (Ψ j).marks) c →
        Blocked a.floor a.marks (fun j => (Ψ j).floor) c) :
      EntDeriv ![a] Ψ
  /-- The matching rule: one conclusion disjunct sits below the premise
  atom in the compiled refinement order.  No satisfiability hypothesis:
  the sound direction of the compiled order never needed one. -/
  | matching {m : ℕ} (a : SpecAtom K) (Ψ : Fin m → SpecAtom K) (j : Fin m)
      (hfloor : (Ψ j).floor ≤ a.floor)
      (hcov : ∀ v' ∈ (Ψ j).marks, ∃ v ∈ a.marks, v ≤ a.floor ⊔ v') :
      EntDeriv ![a] Ψ
  /-- The splitting rule: under a shared floor, one demand refines into
  a family, with the side condition one pointwise domination row
  against the join. -/
  | splitting {m : ℕ} (u w : K → ℝ≥0∞) (wj : Fin m → K → ℝ≥0∞)
      (hle : w ≤ u ⊔ ⨆ j, wj j) :
      EntDeriv ![SpecAtom.single u w] (fun j => SpecAtom.single u (wj j))
  /-- Conclusion-side structural rule: re-index the conclusion family
  along any map — weakening, permutation, and contraction at once. -/
  | reindex {n m m' : ℕ} {Φ : Fin n → SpecAtom K} {Ψ : Fin m → SpecAtom K}
      {Ψ' : Fin m' → SpecAtom K} (ρ : Fin m → Fin m')
      (hρ : ∀ j, Ψ' (ρ j) = Ψ j) (h : EntDeriv Φ Ψ) :
      EntDeriv Φ Ψ'
  /-- Premise-side structural rule: a disjunction entails what each of
  its disjuncts entails. -/
  | split {n m : ℕ} {Φ : Fin n → SpecAtom K} {Ψ : Fin m → SpecAtom K}
      (h : ∀ i, EntDeriv ![Φ i] Ψ) :
      EntDeriv Φ Ψ

/-- The blocking side condition yields the model-class inclusion: the
soundness direction of the blocking criterion, at the unrestricted
system class (hence over every class of systems). -/
theorem blocked_famClass_subset {m : ℕ} {a : SpecAtom K}
    {Ψ : Fin m → SpecAtom K}
    (h : ∀ c, SelValid (fun j => (Ψ j).marks) c →
      Blocked a.floor a.marks (fun j => (Ψ j).floor) c) :
    famClass ![a] ⊆ famClass Ψ := by
  intro σ hσ
  rw [famClass_singleton] at hσ
  obtain ⟨j, hj⟩ := (coupled_union_refinement_iff (P := fun _ => True)
    (fun _ _ => trivial)).mpr h σ trivial hσ
  exact Set.mem_iUnion.mpr ⟨j, hj⟩

/-- **Soundness of the entailment species** against the coupled
judgment, over the unrestricted system class: every derivable sequent's
premise class is contained in its conclusion class.  All three
introduction rules discharge through the blocking criterion. -/
theorem EntDeriv.sound {n m : ℕ} {Φ : Fin n → SpecAtom K}
    {Ψ : Fin m → SpecAtom K} (h : EntDeriv Φ Ψ) :
    famClass Φ ⊆ famClass Ψ := by
  induction h with
  | blocking a Ψ hb => exact blocked_famClass_subset hb
  | matching a Ψ j hfloor hcov =>
      exact blocked_famClass_subset fun c hc =>
        matching_blocked hfloor hcov c hc
  | splitting u w wj hle =>
      exact blocked_famClass_subset fun c hc =>
        splitting_blocked hle c hc
  | reindex ρ hρ h ih =>
      intro σ hσ
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (ih hσ)
      refine Set.mem_iUnion.mpr ⟨ρ j, ?_⟩
      rw [hρ j]
      exact hj
  | split h ih =>
      intro σ hσ
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hσ
      refine ih i ?_
      rw [famClass_singleton]
      exact hi

/-- Soundness restricted to any class of systems — a special case of
`EntDeriv.sound`, stated for the citizen-class reading. -/
theorem EntDeriv.sound_class {P : (K → ℝ≥0∞) → Prop} {n m : ℕ}
    {Φ : Fin n → SpecAtom K} {Ψ : Fin m → SpecAtom K}
    (h : EntDeriv Φ Ψ) :
    ∀ σ, P σ → σ ∈ famClass Φ → σ ∈ famClass Ψ :=
  fun _ _ hσ => h.sound hσ

/-! ## Completeness, and the admissible rules -/

/-- **Completeness at the unrestricted class**: a semantically valid
entailment is derivable — one premise `split`, then per-disjunct
`blocking`.  The completeness direction of the blocking criterion,
packaged as derivability. -/
theorem entDeriv_of_famClass_subset {n m : ℕ} {Φ : Fin n → SpecAtom K}
    {Ψ : Fin m → SpecAtom K} (h : famClass Φ ⊆ famClass Ψ) :
    EntDeriv Φ Ψ := by
  refine .split fun i => .blocking (Φ i) Ψ ?_
  refine (coupled_union_refinement_iff (P := fun _ => True)
    (fun _ _ => trivial)).mp ?_
  intro σ _ hsat
  exact mem_famClass_iff.mp (h (Set.mem_iUnion.mpr ⟨i, hsat⟩))

/-- **Class-parametric completeness**: validity over any class of
systems containing the canonical adversaries already forces
derivability. -/
theorem entDeriv_of_valid {P : (K → ℝ≥0∞) → Prop} {n m : ℕ}
    {Φ : Fin n → SpecAtom K} {Ψ : Fin m → SpecAtom K}
    (hPc : ∀ (i : Fin n) c, SelValid (fun j => (Ψ j).marks) c →
      P (selSup (Φ i).floor c))
    (h : ∀ σ, P σ → σ ∈ famClass Φ → σ ∈ famClass Ψ) :
    EntDeriv Φ Ψ := by
  refine .split fun i => .blocking (Φ i) Ψ ?_
  refine (coupled_union_refinement_iff (P := P) (hPc i)).mp ?_
  intro σ hP hsat
  exact mem_famClass_iff.mp (h σ hP (Set.mem_iUnion.mpr ⟨i, hsat⟩))

/-- Reflexivity is derived: identity matching, per disjunct. -/
theorem EntDeriv.refl {n : ℕ} (Φ : Fin n → SpecAtom K) :
    EntDeriv Φ Φ :=
  .split fun i => .matching (Φ i) Φ i le_rfl
    fun v' hv' => ⟨v', hv', le_sup_right⟩

/-- **Cut is admissible with no side hypotheses**: compose the two
soundness facts and re-derive by completeness.  Admissibility inherited
from completeness, not proved by permutation of rules. -/
theorem EntDeriv.cut {n m k : ℕ} {Φ : Fin n → SpecAtom K}
    {Ψ : Fin m → SpecAtom K} {Θ : Fin k → SpecAtom K}
    (h₁ : EntDeriv Φ Ψ) (h₂ : EntDeriv Ψ Θ) : EntDeriv Φ Θ :=
  entDeriv_of_famClass_subset (h₁.sound.trans h₂.sound)

/-- **Ex falso at the entailment level is derived, not postulated**: an
unsatisfiable premise atom entails every conclusion family, because
some demand sits at or below the floor and that demand blocks every
selection — the blocking rule alone suffices, and the calculus ships
no ex-falso rule. -/
theorem EntDeriv.of_not_con {a : SpecAtom K}
    (h : ¬ Con a.floor a.marks) {m : ℕ} (Ψ : Fin m → SpecAtom K) :
    EntDeriv ![a] Ψ := by
  have h' : ∃ v ∈ a.marks, v ≤ a.floor := by
    by_contra hc
    push Not at hc
    exact h fun v hv => dip_iff_not_le.mpr (hc v hv)
  obtain ⟨v, hv, hvle⟩ := h'
  exact .blocking a Ψ fun c _ =>
    Or.inl ⟨v, hv, hvle.trans le_selSup_left⟩

/-! ## The satisfaction species -/

/-- **Satisfaction sequents**: derivations placing a system inside a
finite disjunction of atoms.  Two rules: the certificate introduction
(`intro` — a disjunct index, one safety row, one dip witness per mark)
and refinement transport along a derivable entailment (`transport`).
The freest-model introduction is the degenerate `intro`
(`satDeriv_self_of_con`). -/
inductive SatDeriv {K : Type u} (σ : K → ℝ≥0∞) :
    ∀ {n : ℕ}, (Fin n → SpecAtom K) → Prop where
  /-- Certificate introduction: a disjunct index, the safety row, and
  one dip witness per liveness mark. -/
  | intro {n : ℕ} {Φ : Fin n → SpecAtom K} (i : Fin n)
      (hsafe : (Φ i).floor ≤ σ)
      (hdip : ∀ v ∈ (Φ i).marks, Dip σ v) :
      SatDeriv σ Φ
  /-- Refinement transport along a derivable entailment. -/
  | transport {n m : ℕ} {Φ : Fin n → SpecAtom K} {Ψ : Fin m → SpecAtom K}
      (h : SatDeriv σ Φ) (e : EntDeriv Φ Ψ) :
      SatDeriv σ Ψ

/-- **Soundness of the satisfaction species**: a derivable satisfaction
sequent is a satisfaction — some disjunct's coupled judgment holds. -/
theorem SatDeriv.sound {σ : K → ℝ≥0∞} {n : ℕ} {Φ : Fin n → SpecAtom K}
    (h : SatDeriv σ Φ) :
    ∃ i, CoupledSat σ (Φ i).floor (Φ i).marks := by
  induction h with
  | intro i hsafe hdip => exact ⟨i, hsafe, hdip⟩
  | transport h e ih =>
      obtain ⟨i, hi⟩ := ih
      exact mem_famClass_iff.mp (e.sound (Set.mem_iUnion.mpr ⟨i, hi⟩))

/-- The freest-model introduction, derived: a satisfiable atom's own
floor derives the sequent, with the con condition supplying every dip. -/
theorem satDeriv_self_of_con {n : ℕ} {Φ : Fin n → SpecAtom K}
    (i : Fin n) (h : Con (Φ i).floor (Φ i).marks) :
    SatDeriv ((Φ i).floor) Φ :=
  .intro i le_rfl h

/-- **The properness presupposition is a theorem of the calculus**:
every derivable satisfaction sequent's system realizes some point at
finite penalty.  To satisfy anything, first exist — carried by the
structural properness demand in every atom's liveness slot. -/
theorem SatDeriv.proper {σ : K → ℝ≥0∞} {n : ℕ}
    {Φ : Fin n → SpecAtom K} (h : SatDeriv σ Φ) : ∃ μ, σ μ ≠ ⊤ := by
  obtain ⟨i, -, hlive⟩ := h.sound
  exact (hlive ⊤ (Φ i).top_mem).proper

/-- **The inconsistent system derives nothing** — inversion at the
derivation level, with no side condition on the conclusion family:
under the option-A shape every liveness slot is inhabited, so the
hypothesis-free statement holds. -/
theorem not_satDeriv_top {n : ℕ} {Φ : Fin n → SpecAtom K} :
    ¬ SatDeriv (⊤ : K → ℝ≥0∞) Φ := by
  intro h
  obtain ⟨μ, hμ⟩ := h.proper
  exact hμ (Pi.top_apply μ)

/-! ## The bridge to the presentation type -/

/-- The presentation of an indexed atom family. -/
def SpecDnf.ofFam {n : ℕ} (Φ : Fin n → SpecAtom K) : SpecDnf K where
  atoms := Set.range Φ
  finite_atoms := Set.finite_range Φ

/-- The bridge is class-exact: the presentation of a family has the
family's model class. -/
@[simp] theorem SpecDnf.ofFam_modelClass {n : ℕ}
    (Φ : Fin n → SpecAtom K) :
    (SpecDnf.ofFam Φ).modelClass = famClass Φ := by
  rw [SpecDnf.modelClass, famClass]
  exact Set.biUnion_range

/-- Every presentation arises from an indexed family: the calculus's
sequent sides cover the presentation type. -/
theorem SpecDnf.exists_ofFam_eq (D : SpecDnf K) :
    ∃ (n : ℕ) (Φ : Fin n → SpecAtom K), SpecDnf.ofFam Φ = D := by
  obtain ⟨n, f, hf⟩ := D.finite_atoms.fin_embedding
  exact ⟨n, f, SpecDnf.ext hf⟩

section Hyperspace

variable {V : Type*} [Fintype V] [Nonempty V]

/-- **The system boundary lands in the constructible class**: a
derivable satisfaction sequent places the citizen's body in the
hyperspace class of its spec. -/
theorem SatDeriv.compileNC_mem {σ : ProbPenalty V}
    (hσ : LowerSemicontinuous σ) {n : ℕ}
    {Φ : Fin n → SpecAtom (ProbState V)} (h : SatDeriv σ Φ) :
    compileNC σ hσ ∈
      dnfClass (fun i => (Φ i).floor) (fun i => (Φ i).marks) :=
  (compileNC_mem_dnfClass_iff hσ).mpr h.sound

end Hyperspace

end SuFunctor.Universe
