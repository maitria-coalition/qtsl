import SuFunctor.Universe.SpecElab
import SuFunctor.Universe.RecordLensContinuum
import SuFunctor.Universe.TopologicalCitizenship
import SuFunctor.Universe.ReachAvoid
import SuFunctor.Adequacy.SpecBehavioral

/-! # Path-formula formers over the record lens

The path fragment of the specification language — invariance, bounded
invariance, bounded reach, safety-until-a-deadline, Streett acceptance,
and surface path negation — compiled into **record-space classes over
the lens site**: the con-coupled pairs of a stage graph and an
occupation measure carried by `SuFunctor.Universe.RecordLens`.

The organizing observations:

* **Every path former here reads only the set of occupied stages.**
  The lens offers two readers of that set — the graph (`touch` species)
  and the support of the occupation measure (`dwell` species) — and the
  con condition of the record lens says *exactly* that the dwell reader
  is contained in the touch reader (`recordCon_iff_stages`).  Each
  former's species-transport direction is therefore read off its
  variance in the occupied-stage set: invariance formers are antitone
  (touch-certified transports to the dwell claim), reach formers are
  monotone (the transport flips), and the mixed formers (until,
  Streett) transport in *neither* direction — witnessed by explicit
  con-coupled separations, so the absence of those transports is
  content, not omission.
* **Polarity dictates the judgment face.**  Invariance classes enter
  the coupled judgment on the safety floor (`wallOn`, the ∀-face);
  reach classes enter on the liveness marks (`markOn`, the ∃-face —
  new here, the mark twin of the wall).  The properness demand `⊤` is
  the `Set.univ` instance of the localized liveness mark
  (`markOn_univ`): every "eventually" claim generalizes the bare
  existence claim by localizing its goal.  The general record atom
  (`pathAtom`) carries one safety class and one liveness class, and
  its satisfaction is *safe and proper-into-the-goal*
  (`coupledSat_pathAtom_iff`).
* **The horizon of a windowed former is a natural number.**  The
  finitary record site is tick-indexed (`τ : X → ℕ`) and unitless, so
  the windows of bounded invariance, bounded reach, and until admit no
  rational reading at this stratum — the same forcing that types the
  summed-return horizon in `SpecBehavioral`.  (Duration-typed rational
  horizons stay honest at clocked continuum strata, which are not this
  module's windowed target.)
* **Negation is resolved by the normal form, and the fence table is
  executable.**  Surface path negation consumes exactly the spellable
  duals — negated bounded invariance *is* bounded reach of the
  complement, at both parities — and refuses the three residues with
  a named address (negated unbounded invariance, negated until,
  negated Streett), as `Except` values rather than prose.  The refusal
  of negated unbounded invariance is grammar economy (there is no
  unbounded-reach former to spell the dual, a deliberate absence), not
  semantic inexpressibility: the record-class complement exists
  (`not_alwaysOn_iff`) — in contrast to the spec-class stratum one
  level up, where no class has an expressible complement.
* **Deterministic records collapse the species.**  At the canonical
  (uniform) lift of a graph the two stage readers coincide
  (`stages_uniformLift`), so every class of every former is
  species-independent there, and the compile agrees with the
  trajectory semantics of the specification catalogue on the nose
  (`alwaysOn_trajStages_iff` and kin) — the exact deterministic cells;
  the stochastic tier keeps only the directed transports above.
* **Citizenship.**  Invariance classes are closed, reach classes are
  open, and the until and Streett classes are *constructible* — finite
  unions of locally closed pieces (until is the grammar's first
  genuinely constructible-not-closed-not-open class; its window
  decomposition is `recordClass_untilF_eq`).  With the generic wall
  and mark citizenship lemmas, every compiled record atom has a
  lower-semicontinuous floor and lower-semicontinuous marks.

Deliberately not claimed: the pasting between the record tier and the
kernel path measure (where the quantitative Streett bundle concludes)
is the finite-dimensional-distributions stratum, exactly the fence
`SpecBehavioral` states; and the record class of Streett acceptance is
the occupation shadow of the infinitary acceptance condition — a
finite record has no "infinitely often".

Axiom receipts at the bottom; expected closure ⊆ [propext,
Classical.choice, Quot.sound], zero sorryAx. -/

namespace SuFunctor.Universe

open scoped ENNReal
open TopologicalSpace

universe u v

/-! ## The ∃-face judgment cells: marks, and the general record atom -/

section MarkCells

variable {K : Type u}

open Classical in
/-- The liveness mark of a goal class: `⊤` on the goal, `0` off it —
the mark twin of `wallOn`.  A dip under it is a permitted point *in
the goal* (`dip_markOn_iff`); the properness demand is its `Set.univ`
instance (`markOn_univ`). -/
noncomputable def markOn (C : Set K) : K → ℝ≥0∞ :=
  fun μ => if μ ∈ C then ⊤ else 0

theorem markOn_apply_of_mem {C : Set K} {μ : K} (h : μ ∈ C) :
    markOn C μ = ⊤ := by simp [markOn, h]

theorem markOn_apply_of_not_mem {C : Set K} {μ : K} (h : μ ∉ C) :
    markOn C μ = 0 := by simp [markOn, h]

/-- **The properness demand is the `univ` instance of the localized
liveness mark**: "eventually ⊤" is the goal-class `Set.univ` case of
"eventually the goal". -/
@[simp] theorem markOn_univ : markOn (Set.univ : Set K) = ⊤ := by
  funext μ
  rw [markOn_apply_of_mem (Set.mem_univ μ), Pi.top_apply]

theorem markOn_mono {C D : Set K} (h : C ⊆ D) : markOn C ≤ markOn D := by
  intro μ
  by_cases hμ : μ ∈ C
  · rw [markOn_apply_of_mem hμ, markOn_apply_of_mem (h hμ)]
  · rw [markOn_apply_of_not_mem hμ]
    exact zero_le

/-- **The dip reading of a liveness mark**: a system dips under the
goal's mark iff it permits some point of the goal. -/
theorem dip_markOn_iff {C : Set K} {σ : K → ℝ≥0∞} :
    Dip σ (markOn C) ↔ (permitted σ ∩ C).Nonempty := by
  constructor
  · rintro ⟨μ, hμ⟩
    by_cases hC : μ ∈ C
    · rw [markOn_apply_of_mem hC] at hμ
      exact ⟨μ, lt_top_iff_ne_top.mp hμ, hC⟩
    · rw [markOn_apply_of_not_mem hC] at hμ
      exact absurd hμ (not_lt.mpr zero_le)
  · rintro ⟨μ, hperm, hC⟩
    refine ⟨μ, ?_⟩
    rw [markOn_apply_of_mem hC]
    exact lt_top_iff_ne_top.mpr hperm

/-- The general record atom: one safety class on the floor, one
liveness class among the marks.  One spec may carry an invariance
clause and a reach clause; this is that atom, with the properness
demand riding by construction. -/
noncomputable def pathAtom (C G : Set K) : SpecAtom K where
  floor := wallOn C
  marks := {markOn G, ⊤}
  finite_marks := (Set.finite_singleton _).insert _
  top_mem := Set.mem_insert_of_mem _ rfl

@[simp] theorem pathAtom_floor (C G : Set K) :
    (pathAtom C G).floor = wallOn C := rfl

@[simp] theorem pathAtom_marks (C G : Set K) :
    (pathAtom C G).marks = {markOn G, ⊤} := rfl

/-- The class semantics of the general record atom: safe into `C`,
proper into `G`. -/
def safeLive (C G : Set K) : Set (K → ℝ≥0∞) :=
  {σ | permitted σ ⊆ C ∧ (permitted σ ∩ G).Nonempty}

theorem mem_safeLive_iff {C G : Set K} {σ : K → ℝ≥0∞} :
    σ ∈ safeLive C G ↔ permitted σ ⊆ C ∧ (permitted σ ∩ G).Nonempty :=
  Iff.rfl

/-- **Satisfying the general record atom is being safe AND proper into
the goal**: the presupposition cell of `SpecElab`, with the existence
demand localized. -/
theorem coupledSat_pathAtom_iff {C G : Set K} {σ : K → ℝ≥0∞} :
    CoupledSat σ (pathAtom C G).floor (pathAtom C G).marks ↔
      permitted σ ⊆ C ∧ (permitted σ ∩ G).Nonempty := by
  unfold CoupledSat
  rw [pathAtom_floor, pathAtom_marks, wallOn_le_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    exact dip_markOn_iff.mp (h _ (Set.mem_insert _ _))
  · intro h v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · exact dip_markOn_iff.mpr h
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact (dip_markOn_iff.mpr h).mono_mark le_top

theorem pathAtom_modelClass (C G : Set K) :
    (pathAtom C G).modelClass = safeLive C G := by
  ext σ
  exact coupledSat_pathAtom_iff

/-- Degenerate liveness recovers the safety class: proper-into-`univ`
is bare properness. -/
theorem safeLive_univ_right (C : Set K) :
    safeLive C Set.univ = safeProper C := by
  ext σ
  rw [mem_safeLive_iff, mem_safeProper_iff, Set.inter_univ]

/-- The doubly-degenerate atom is the bare feasibility spec. -/
theorem pathAtom_univ_modelClass :
    (pathAtom (Set.univ : Set K) Set.univ).modelClass
      = safeProper Set.univ := by
  rw [pathAtom_modelClass, safeLive_univ_right]

/-- The class is monotone in both regions. -/
theorem safeLive_mono {C C' G G' : Set K} (hC : C ⊆ C') (hG : G ⊆ G') :
    safeLive C G ⊆ safeLive C' G' := by
  rintro σ ⟨hsub, μ, hμp, hμG⟩
  exact ⟨hsub.trans hC, μ, hμp, hG hμG⟩

/-- **The ∃-face directed-cell template**: region inclusions on both
faces transport to a model-class inclusion of the general record
atoms — the liveness twin of `safetyAtom_modelClass_mono`.  `sound`
direction only; strict inclusions stay strict. -/
theorem pathAtom_modelClass_mono {C C' G G' : Set K} (hC : C ⊆ C')
    (hG : G ⊆ G') :
    (pathAtom C G).modelClass ⊆ (pathAtom C' G').modelClass := by
  rw [pathAtom_modelClass, pathAtom_modelClass]
  exact safeLive_mono hC hG

/-- The relativized transport: when every permitted point lies in a
reference class `R`, inclusions that hold only *on* `R` still
transport.  Consumed at `R := recordCon` by the species squares. -/
theorem safeLive_mono_on {R C C' G G' : Set K} {σ : K → ℝ≥0∞}
    (hR : permitted σ ⊆ R) (hC : R ∩ C ⊆ C') (hG : R ∩ G ⊆ G')
    (h : σ ∈ safeLive C G) : σ ∈ safeLive C' G' := by
  obtain ⟨hsub, μ, hμp, hμG⟩ := h
  exact ⟨fun ν hν => hC ⟨hR hν, hsub hν⟩, μ, hμp, hG ⟨hR hμp, hμG⟩⟩

end MarkCells

/-! ### Citizenship of walls and marks, generically -/

section WallMarkCitizenship

variable {K : Type u} [TopologicalSpace K]

/-- The wall of a **closed** class is a citizen: its escape set is
open. -/
theorem lowerSemicontinuous_wallOn_of_isClosed {C : Set K}
    (hC : IsClosed C) : LowerSemicontinuous (wallOn C) := by
  classical
  refine lowerSemicontinuous_wall_on_open (S := Cᶜ)
    hC.isOpen_compl (fun μ hμ => wallOn_apply_of_not_mem hμ)
    (fun μ hμ => wallOn_apply_of_mem (not_not.mp hμ))

/-- The mark of an **open** goal class is a citizen: the polarity dual
of the wall lemma. -/
theorem lowerSemicontinuous_markOn_of_isOpen {G : Set K}
    (hG : IsOpen G) : LowerSemicontinuous (markOn G) := by
  classical
  refine lowerSemicontinuous_wall_on_open (S := G)
    hG (fun μ hμ => markOn_apply_of_mem hμ)
    (fun μ hμ => markOn_apply_of_not_mem hμ)

end WallMarkCitizenship

/-! ## The stage-set combinators

Each path former, read as a predicate on the set of occupied stages —
no lens yet, no topology: a plain type of stages `X` with a tick
coordinate `τ : X → ℕ`.  The windowed combinators take a **natural**
horizon: the stratum is tick-indexed and unitless. -/

section Combinators

variable {X : Type v}

/-- Invariance: every occupied stage is good. -/
def alwaysOn (Good : Set X) (S : Set X) : Prop := S ⊆ Good

/-- Bounded invariance: every occupied stage within the window is
good. -/
def windowAlwaysOn (τ : X → ℕ) (n : ℕ) (Good : Set X) (S : Set X) :
    Prop :=
  ∀ x ∈ S, τ x ≤ n → x ∈ Good

/-- Bounded reach: some occupied stage within the window is in the
goal. -/
def windowReachOn (τ : X → ℕ) (n : ℕ) (Goal : Set X) (S : Set X) :
    Prop :=
  ∃ x ∈ S, τ x ≤ n ∧ x ∈ Goal

/-- Safety until a deadline: some tick within the window carries an
occupied target stage, and every occupied stage strictly before that
tick is safe. -/
def untilOn (τ : X → ℕ) (n : ℕ) (Safe Target : Set X) (S : Set X) :
    Prop :=
  ∃ t ≤ n, (∃ x ∈ S, τ x = t ∧ x ∈ Target) ∧
    ∀ x ∈ S, τ x < t → x ∈ Safe

/-- Streett acceptance, occupation form: every requested pair is
answered — occupation of the request region forces occupation of the
response region.  (The finite-record shadow of the infinitary
acceptance condition.) -/
def streettOn (prs : List (Set X × Set X)) (S : Set X) : Prop :=
  ∀ pr ∈ prs, (∃ x ∈ S, x ∈ pr.1) → ∃ x ∈ S, x ∈ pr.2

@[simp] theorem streettOn_nil {S : Set X} :
    streettOn ([] : List (Set X × Set X)) S := by
  intro pr hpr
  simp at hpr

theorem streettOn_cons {pr : Set X × Set X}
    {prs : List (Set X × Set X)} {S : Set X} :
    streettOn (pr :: prs) S ↔
      ((∃ x ∈ S, x ∈ pr.1) → ∃ x ∈ S, x ∈ pr.2) ∧ streettOn prs S := by
  constructor
  · intro h
    exact ⟨h pr (by simp),
      fun pr' hpr' => h pr' (List.mem_cons_of_mem pr hpr')⟩
  · rintro ⟨hhd, htl⟩ pr' hpr'
    rcases List.mem_cons.mp hpr' with rfl | hpr'
    · exact hhd
    · exact htl pr' hpr'

/-! ### Variance in the occupied-stage set

Invariance formers are antitone, reach formers monotone; until and
Streett are mixed and have **no** stage-set monotonicity — the
separations at the lens witness the absence. -/

theorem alwaysOn_anti {Good S S' : Set X} (hS : S' ⊆ S)
    (h : alwaysOn Good S) : alwaysOn Good S' :=
  hS.trans h

theorem windowAlwaysOn_anti {τ : X → ℕ} {n : ℕ} {Good S S' : Set X}
    (hS : S' ⊆ S) (h : windowAlwaysOn τ n Good S) :
    windowAlwaysOn τ n Good S' :=
  fun x hx => h x (hS hx)

theorem windowReachOn_mono {τ : X → ℕ} {n : ℕ} {Goal S S' : Set X}
    (hS : S ⊆ S') (h : windowReachOn τ n Goal S) :
    windowReachOn τ n Goal S' := by
  obtain ⟨x, hx, hτ, hG⟩ := h
  exact ⟨x, hS hx, hτ, hG⟩

/-! ### Approximation sources: window and region faces -/

theorem windowReachOn_mono_window {τ : X → ℕ} {n n' : ℕ}
    {Goal S : Set X} (hn : n ≤ n') (h : windowReachOn τ n Goal S) :
    windowReachOn τ n' Goal S := by
  obtain ⟨x, hx, hτ, hG⟩ := h
  exact ⟨x, hx, hτ.trans hn, hG⟩

theorem windowAlwaysOn_anti_window {τ : X → ℕ} {n n' : ℕ}
    {Good S : Set X} (hn : n ≤ n') (h : windowAlwaysOn τ n' Good S) :
    windowAlwaysOn τ n Good S :=
  fun x hx hτ => h x hx (hτ.trans hn)

theorem untilOn_mono_window {τ : X → ℕ} {n n' : ℕ}
    {Safe Target S : Set X} (hn : n ≤ n')
    (h : untilOn τ n Safe Target S) : untilOn τ n' Safe Target S := by
  obtain ⟨t, ht, hhit, hsafe⟩ := h
  exact ⟨t, ht.trans hn, hhit, hsafe⟩

theorem windowReachOn_mono_region {τ : X → ℕ} {n : ℕ}
    {Goal Goal' S : Set X} (hG : Goal ⊆ Goal')
    (h : windowReachOn τ n Goal S) : windowReachOn τ n Goal' S := by
  obtain ⟨x, hx, hτ, hGx⟩ := h
  exact ⟨x, hx, hτ, hG hGx⟩

theorem windowAlwaysOn_mono_region {τ : X → ℕ} {n : ℕ}
    {Good Good' S : Set X} (hG : Good ⊆ Good')
    (h : windowAlwaysOn τ n Good S) : windowAlwaysOn τ n Good' S :=
  fun x hx hτ => hG (h x hx hτ)

theorem untilOn_mono_safe {τ : X → ℕ} {n : ℕ}
    {Safe Safe' Target S : Set X} (hS : Safe ⊆ Safe')
    (h : untilOn τ n Safe Target S) : untilOn τ n Safe' Target S := by
  obtain ⟨t, ht, hhit, hsafe⟩ := h
  exact ⟨t, ht, hhit, fun x hx hτ => hS (hsafe x hx hτ)⟩

theorem untilOn_mono_target {τ : X → ℕ} {n : ℕ}
    {Safe Target Target' S : Set X} (hT : Target ⊆ Target')
    (h : untilOn τ n Safe Target S) : untilOn τ n Safe Target' S := by
  obtain ⟨t, ht, ⟨x, hx, hτx, hTx⟩, hsafe⟩ := h
  exact ⟨t, ht, ⟨x, hx, hτx, hT hTx⟩, hsafe⟩

/-- Response enlargement, request fixed, pairwise along the list. -/
theorem streettOn_mono {prs prs' : List (Set X × Set X)} {S : Set X}
    (hp : List.Forall₂ (fun pr pr' => pr.1 = pr'.1 ∧ pr.2 ⊆ pr'.2)
      prs prs')
    (h : streettOn prs S) : streettOn prs' S := by
  induction hp with
  | nil => exact streettOn_nil
  | @cons pr pr' _ _ hhd _ ih =>
    rw [streettOn_cons] at h ⊢
    obtain ⟨hfst, htl⟩ := h
    refine ⟨fun hreq => ?_, ih htl⟩
    obtain ⟨x, hx, hresp⟩ := hfst (hhd.1 ▸ hreq)
    exact ⟨x, hx, hhd.2 hresp⟩

/-- **Bounded reach is trivially-safe until**: the derived-spelling
coherence cell. -/
theorem untilOn_univ_safe {τ : X → ℕ} {n : ℕ} {Target S : Set X} :
    untilOn τ n Set.univ Target S ↔ windowReachOn τ n Target S := by
  constructor
  · rintro ⟨t, ht, ⟨x, hx, hτx, hTx⟩, -⟩
    exact ⟨x, hx, hτx ▸ ht, hTx⟩
  · rintro ⟨x, hx, hτ, hTx⟩
    exact ⟨τ x, hτ, ⟨x, hx, rfl, hTx⟩, fun y _ _ => Set.mem_univ y⟩

/-! ### The dualities: what surface path negation consumes

Negated bounded invariance is bounded reach of the complement — the
one always-spellable dual, at both parities.  The unbounded dual also
*exists* at the record site (`not_alwaysOn_iff`); the surface grammar
refuses it because no unbounded-reach former exists to spell it — a
deliberate absence of the catalogue, not a semantic gap of the site.
(The spec-*class* stratum one level up genuinely has no expressible
complements; that is a different — and stronger — fact.) -/

theorem not_windowAlwaysOn_iff {τ : X → ℕ} {n : ℕ} {Good S : Set X} :
    ¬ windowAlwaysOn τ n Good S ↔ windowReachOn τ n Goodᶜ S := by
  unfold windowAlwaysOn windowReachOn
  push Not
  simp only [Set.mem_compl_iff]

theorem not_windowReachOn_iff {τ : X → ℕ} {n : ℕ} {Goal S : Set X} :
    ¬ windowReachOn τ n Goal S ↔ windowAlwaysOn τ n Goalᶜ S := by
  unfold windowAlwaysOn windowReachOn
  push Not
  simp only [Set.mem_compl_iff]

theorem not_alwaysOn_iff {Good S : Set X} :
    ¬ alwaysOn Good S ↔ ∃ x ∈ S, x ∈ Goodᶜ := by
  rw [alwaysOn, Set.not_subset]
  simp only [Set.mem_compl_iff]

/-! ### Window normal forms (consumed by the citizenship rows) -/

theorem windowAlwaysOn_iff_subset {τ : X → ℕ} {n : ℕ}
    {Good S : Set X} :
    windowAlwaysOn τ n Good S ↔ S ⊆ Good ∪ {x | n < τ x} := by
  constructor
  · intro h x hx
    by_cases hτ : τ x ≤ n
    · exact Or.inl (h x hx hτ)
    · exact Or.inr (not_le.mp hτ)
  · intro h x hx hτ
    rcases h hx with hG | hlate
    · exact hG
    · exact absurd hτ (not_le.mpr hlate)

theorem windowReachOn_iff_inter {τ : X → ℕ} {n : ℕ}
    {Goal S : Set X} :
    windowReachOn τ n Goal S ↔
      (S ∩ (Goal ∩ {x | τ x ≤ n})).Nonempty := by
  constructor
  · rintro ⟨x, hx, hτ, hG⟩
    exact ⟨x, hx, hG, hτ⟩
  · rintro ⟨x, hx, hG, hτ⟩
    exact ⟨x, hx, hτ, hG⟩

/-- The window decomposition of until: finitely many tick candidates,
each an (occupied-target-at-the-tick) ∩ (safe-strictly-before)
conjunction. -/
theorem untilOn_iff_exists_fin {τ : X → ℕ} {n : ℕ}
    {Safe Target S : Set X} :
    untilOn τ n Safe Target S ↔
      ∃ t : Fin (n + 1),
        (S ∩ (Target ∩ {x | τ x = (t : ℕ)})).Nonempty ∧
          S ⊆ Safe ∪ {x | ¬ τ x < (t : ℕ)} := by
  constructor
  · rintro ⟨t, ht, ⟨x, hx, hτx, hTx⟩, hsafe⟩
    refine ⟨⟨t, Nat.lt_succ_of_le ht⟩, ⟨x, hx, hTx, hτx⟩, fun y hy => ?_⟩
    by_cases hτy : τ y < t
    · exact Or.inl (hsafe y hy hτy)
    · exact Or.inr hτy
  · rintro ⟨t, ⟨x, hx, hTx, hτx⟩, hsafe⟩
    refine ⟨(t : ℕ), Nat.lt_succ_iff.mp t.isLt, ⟨x, hx, hτx, hTx⟩,
      fun y hy hτy => ?_⟩
    rcases hsafe hy with hS | hlate
    · exact hS
    · exact absurd hτy hlate

end Combinators

/-! ## The path grammar, its normal form, and the fence table -/

section Grammar

variable {α : Type v}

/-- A request/response pair of Streett acceptance.  **Polarity is
constructor choice, never stored data**: `base` consumes the request
exactly; `cmpl` consumes it through the complement (stored positive).
The base-stratum policing of a `base` request is record-level
conformance, upstream of this module. -/
inductive StreettPair (α : Type v) : Type v
  | base (req resp : StateFormula α) : StreettPair α
  | cmpl (req resp : StateFormula α) : StreettPair α

namespace StreettPair

/-- The request region: exact for `base`, complemented for `cmpl`. -/
def reqRegion {X : Type*} (A : α → Set X) : StreettPair α → Set X
  | base req _ => req.den A
  | cmpl req _ => (req.den A)ᶜ

/-- The response region. -/
def respRegion {X : Type*} (A : α → Set X) : StreettPair α → Set X
  | base _ resp => resp.den A
  | cmpl _ resp => resp.den A

/-- Both regions, as the pair the occupation combinator reads. -/
def regionPair {X : Type*} (A : α → Set X) (pr : StreettPair α) :
    Set X × Set X :=
  (pr.reqRegion A, pr.respRegion A)

end StreettPair

/-- Negation-free path formulas: the compile's source grammar.  The
windowed horizons are **naturals** — the record site is tick-indexed.
The reach former's flag marks a producer-chosen horizon standing in
for an unbounded reach; it is certificate-reader metadata, not
semantics, and the compile ignores it. -/
inductive PathNnf (α : Type v) : Type v
  | always (φ : StateFormula α) : PathNnf α
  | alwaysT (n : ℕ) (φ : StateFormula α) : PathNnf α
  | deadline (n : ℕ) (φ : StateFormula α) (producerT : Bool) : PathNnf α
  | untilF (n : ℕ) (safe target : StateFormula α) : PathNnf α
  | streett (prs : List (StreettPair α)) : PathNnf α

/-- Surface path formulas: the negation-free formers plus surface path
negation, which the normal form resolves or refuses. -/
inductive PathFormula (α : Type v) : Type v
  | always (φ : StateFormula α) : PathFormula α
  | alwaysT (n : ℕ) (φ : StateFormula α) : PathFormula α
  | deadline (n : ℕ) (φ : StateFormula α) (producerT : Bool) :
      PathFormula α
  | untilF (n : ℕ) (safe target : StateFormula α) : PathFormula α
  | streett (prs : List (StreettPair α)) : PathFormula α
  | notPath (ψ : PathFormula α) : PathFormula α

/-- The three refusal residues of surface path negation, each with its
named address: negated unbounded invariance (no unbounded-reach former
spells the dual — a deliberate absence), negated until (no release
former), negated Streett (Rabin acceptance — the dual judgment,
absent). -/
inductive PathNegResidue : Type
  | negatedAlways : PathNegResidue
  | negatedUntil : PathNegResidue
  | negatedStreett : PathNegResidue
  deriving DecidableEq

/-- The occupied-stage semantics of a negation-free path formula: one
clause per former, each a stage-set combinator over the denoted
regions. -/
def recordPred {X : Type*} (τ : X → ℕ) (A : α → Set X) :
    PathNnf α → Set X → Prop
  | .always φ, S => alwaysOn (φ.den A) S
  | .alwaysT n φ, S => windowAlwaysOn τ n (φ.den A) S
  | .deadline n φ _, S => windowReachOn τ n (φ.den A) S
  | .untilF n sf tg, S => untilOn τ n (sf.den A) (tg.den A) S
  | .streett prs, S => streettOn (prs.map (StreettPair.regionPair A)) S

/-- The occupied-stage semantics of a surface path formula: complement
at negation. -/
def PathFormula.pathSem {X : Type*} (τ : X → ℕ) (A : α → Set X) :
    PathFormula α → Set X → Prop
  | .always φ, S => alwaysOn (φ.den A) S
  | .alwaysT n φ, S => windowAlwaysOn τ n (φ.den A) S
  | .deadline n φ _, S => windowReachOn τ n (φ.den A) S
  | .untilF n sf tg, S => untilOn τ n (sf.den A) (tg.den A) S
  | .streett prs, S => streettOn (prs.map (StreettPair.regionPair A)) S
  | .notPath ψ, S => ¬ ψ.pathSem τ A S

/-- Normal-form resolution by polarity: `pos = false` reads the
formula under an odd number of negations.  The spellable dual —
negated bounded invariance is bounded reach of the complement, and
conversely — resolves; the three residues refuse with their named
address. -/
def pathNnfAux : PathFormula α → Bool → Except PathNegResidue (PathNnf α)
  | .always φ, true => .ok (.always φ)
  | .always _, false => .error .negatedAlways
  | .alwaysT n φ, true => .ok (.alwaysT n φ)
  | .alwaysT n φ, false => .ok (.deadline n φ.neg false)
  | .deadline n φ b, true => .ok (.deadline n φ b)
  | .deadline n φ _, false => .ok (.alwaysT n φ.neg)
  | .untilF n sf tg, true => .ok (.untilF n sf tg)
  | .untilF _ _ _, false => .error .negatedUntil
  | .streett prs, true => .ok (.streett prs)
  | .streett _, false => .error .negatedStreett
  | .notPath ψ, pos => pathNnfAux ψ (!pos)

/-- Normal-form resolution at the surface parity. -/
def pathNnf (ψ : PathFormula α) : Except PathNegResidue (PathNnf α) :=
  pathNnfAux ψ true

/-- **Normal-form resolution is exact on everything it accepts**: at
positive parity the occupied-stage semantics is preserved on the nose;
at negative parity it is complemented on the nose (the spellable
dualities, plus double negation). -/
theorem pathNnfAux_exact {X : Type*} (τ : X → ℕ) (A : α → Set X)
    (ψ : PathFormula α) :
    (∀ χ, pathNnfAux ψ true = .ok χ →
      ∀ S : Set X, recordPred τ A χ S ↔ ψ.pathSem τ A S) ∧
    (∀ χ, pathNnfAux ψ false = .ok χ →
      ∀ S : Set X, recordPred τ A χ S ↔ ¬ ψ.pathSem τ A S) := by
  induction ψ with
  | always φ =>
    constructor
    · intro χ h S
      obtain rfl := Except.ok.inj h
      exact Iff.rfl
    · intro χ h
      simp [pathNnfAux] at h
  | alwaysT n φ =>
    constructor
    · intro χ h S
      obtain rfl := Except.ok.inj h
      exact Iff.rfl
    · intro χ h S
      obtain rfl := Except.ok.inj h
      show windowReachOn τ n (φ.neg.den A) S ↔ _
      exact not_windowAlwaysOn_iff.symm
  | deadline n φ b =>
    constructor
    · intro χ h S
      obtain rfl := Except.ok.inj h
      exact Iff.rfl
    · intro χ h S
      obtain rfl := Except.ok.inj h
      show windowAlwaysOn τ n (φ.den A)ᶜ S ↔ _
      exact not_windowReachOn_iff.symm
  | untilF n sf tg =>
    constructor
    · intro χ h S
      obtain rfl := Except.ok.inj h
      exact Iff.rfl
    · intro χ h
      simp [pathNnfAux] at h
  | streett prs =>
    constructor
    · intro χ h S
      obtain rfl := Except.ok.inj h
      exact Iff.rfl
    · intro χ h
      simp [pathNnfAux] at h
  | notPath ψ ih =>
    constructor
    · intro χ h S
      have h' : pathNnfAux ψ false = .ok χ := h
      rw [ih.2 χ h' S]
      exact Iff.rfl
    · intro χ h S
      have h' : pathNnfAux ψ true = .ok χ := h
      rw [ih.1 χ h' S]
      show ψ.pathSem τ A S ↔ ¬ ¬ ψ.pathSem τ A S
      exact not_not.symm

/-- Exactness at the surface parity. -/
theorem pathNnf_exact {X : Type*} (τ : X → ℕ) (A : α → Set X)
    {ψ : PathFormula α} {χ : PathNnf α} (h : pathNnf ψ = .ok χ)
    (S : Set X) : recordPred τ A χ S ↔ ψ.pathSem τ A S :=
  (pathNnfAux_exact τ A ψ).1 χ h S

/-! ### The fence table, executable -/

/-- Negated unbounded invariance refuses, with its address. -/
@[simp] theorem pathNnf_notPath_always (φ : StateFormula α) :
    pathNnf (PathFormula.notPath (.always φ))
      = .error .negatedAlways := rfl

/-- Negated until refuses, with its address. -/
@[simp] theorem pathNnf_notPath_untilF (n : ℕ)
    (sf tg : StateFormula α) :
    pathNnf (PathFormula.notPath (.untilF n sf tg))
      = .error .negatedUntil := rfl

/-- Negated Streett refuses, with its address (Rabin acceptance — the
dual judgment, a deliberate absence). -/
@[simp] theorem pathNnf_notPath_streett (prs : List (StreettPair α)) :
    pathNnf (PathFormula.notPath (.streett prs))
      = .error .negatedStreett := rfl

/-- **The spellable dual resolves at both parities**: negated bounded
invariance is bounded reach of the complement. -/
@[simp] theorem pathNnf_notPath_alwaysT (n : ℕ) (φ : StateFormula α) :
    pathNnf (PathFormula.notPath (.alwaysT n φ))
      = .ok (.deadline n φ.neg false) := rfl

/-- Double negation consumes through a refused former's dual: the
even parity of a bounded reach resolves. -/
@[simp] theorem pathNnf_notPath_notPath_deadline (n : ℕ)
    (φ : StateFormula α) (b : Bool) :
    pathNnf (PathFormula.notPath (.notPath (.deadline n φ b)))
      = .ok (.deadline n φ b) := rfl

end Grammar

/-! ## The record classes: the two species over the lens -/

section RecordClasses

variable {X : Type u} [Fintype X] [TopologicalSpace X] {α : Type v}

/-- The two readers of the occupied-stage set: the graph face and the
support of the occupation measure.  The species of the record-wall
split, as data. -/
inductive RecordSpecies : Type
  | touch : RecordSpecies
  | dwell : RecordSpecies

/-- The occupied stages, per species. -/
def stages : RecordSpecies → NonemptyCompacts X × ProbState X → Set X
  | .touch, p => (p.1 : Set X)
  | .dwell, p => {x | (p.2 : X → ℝ) x ≠ 0}

@[simp] theorem stages_touch (p : NonemptyCompacts X × ProbState X) :
    stages .touch p = (p.1 : Set X) := rfl

@[simp] theorem stages_dwell (p : NonemptyCompacts X × ProbState X) :
    stages .dwell p = {x | (p.2 : X → ℝ) x ≠ 0} := rfl

variable [DiscreteTopology X]

/-- **The con condition IS the species order**: a lens pair is
con-coupled exactly when its dwell reader is contained in its touch
reader.  Every species-transport direction below is this inclusion
composed with a former's variance. -/
theorem recordCon_iff_stages {p : NonemptyCompacts X × ProbState X} :
    p ∈ recordCon ↔ stages .dwell p ⊆ stages .touch p := by
  rw [mem_recordCon_iff]
  constructor
  · intro h x hx
    exact h x hx
  · intro h x hx
    exact h hx

/-- **The species collapse at canonical lifts**: both readers of a
uniformly-lifted graph are the graph.  Deterministic records make no
species distinction — the root of every exact deterministic cell. -/
theorem stages_uniformLift (sp : RecordSpecies) (G : NonemptyCompacts X) :
    stages sp (G, uniformLift G) = (G : Set X) := by
  cases sp with
  | touch => rfl
  | dwell =>
    ext x
    exact support_uniformLift_iff G x

/-! ### The landed walls are the invariance compile's floors -/

omit [DiscreteTopology X] in
/-- The touch-wall is the wall of the graph-face invariance class. -/
theorem touchWall_eq_wallOn (Bad : Set X) :
    touchWall Bad
      = wallOn {p : NonemptyCompacts X × ProbState X |
          alwaysOn Badᶜ (stages .touch p)} := by
  classical
  funext p
  by_cases h : ((p.1 : Set X) ∩ Bad).Nonempty
  · rw [touchWall, if_pos h, wallOn_apply_of_not_mem]
    intro hmem
    obtain ⟨x, hxG, hxB⟩ := h
    exact hmem hxG hxB
  · rw [touchWall, if_neg h, wallOn_apply_of_mem]
    intro x hxG hxB
    exact h ⟨x, hxG, hxB⟩

omit [DiscreteTopology X] in
/-- The dwell-wall is the wall of the measure-face invariance class. -/
theorem dwellWall_eq_wallOn (Bad : Set X) :
    dwellWall Bad
      = wallOn {p : NonemptyCompacts X × ProbState X |
          alwaysOn Badᶜ (stages .dwell p)} := by
  classical
  funext p
  by_cases h : ∃ x ∈ Bad, (p.2 : X → ℝ) x ≠ 0
  · rw [dwellWall, if_pos h, wallOn_apply_of_not_mem]
    intro hmem
    obtain ⟨x, hxB, hx0⟩ := h
    exact hmem hx0 hxB
  · rw [dwellWall, if_neg h, wallOn_apply_of_mem]
    intro x hx0 hxB
    exact h ⟨x, hxB, hx0⟩

/-! ### The compile, at the class level -/

/-- The record class of a negation-free path formula, per species: the
lens pairs whose occupied stages (read by the species) satisfy the
formula's stage-set predicate. -/
def recordClass (sp : RecordSpecies) (τ : X → ℕ) (A : α → Set X)
    (ψ : PathNnf α) : Set (NonemptyCompacts X × ProbState X) :=
  {p | recordPred τ A ψ (stages sp p)}

omit [DiscreteTopology X] in
theorem mem_recordClass_iff {sp : RecordSpecies} {τ : X → ℕ}
    {A : α → Set X} {ψ : PathNnf α}
    {p : NonemptyCompacts X × ProbState X} :
    p ∈ recordClass sp τ A ψ ↔ recordPred τ A ψ (stages sp p) :=
  Iff.rfl

/-- At a canonical lift, membership is species-independent and reads
the graph directly. -/
theorem mem_recordClass_uniformLift_iff {sp : RecordSpecies}
    {τ : X → ℕ} {A : α → Set X} {ψ : PathNnf α}
    {G : NonemptyCompacts X} :
    (G, uniformLift G) ∈ recordClass sp τ A ψ
      ↔ recordPred τ A ψ (G : Set X) := by
  rw [mem_recordClass_iff, stages_uniformLift]

/-! ### The species transports, and their two-sided absence at the
mixed formers -/

/-- Invariance transports touch → dwell on con-coupled pairs: the
graph-face certificate implies the measure-face claim.  (Antitone
former ∘ con inclusion.) -/
theorem recordClass_touch_subset_dwell_always {τ : X → ℕ}
    {A : α → Set X} (φ : StateFormula α) :
    recordCon ∩ recordClass .touch τ A (.always φ)
      ⊆ recordClass .dwell τ A (.always φ) := by
  rintro p ⟨hcon, h⟩
  exact alwaysOn_anti (recordCon_iff_stages.mp hcon) h

/-- Bounded invariance transports touch → dwell on con-coupled
pairs. -/
theorem recordClass_touch_subset_dwell_alwaysT {τ : X → ℕ}
    {A : α → Set X} (n : ℕ) (φ : StateFormula α) :
    recordCon ∩ recordClass .touch τ A (.alwaysT n φ)
      ⊆ recordClass .dwell τ A (.alwaysT n φ) := by
  rintro p ⟨hcon, h⟩
  exact windowAlwaysOn_anti (recordCon_iff_stages.mp hcon) h

/-- Bounded reach transports dwell → touch on con-coupled pairs: the
transport FLIPS with the former's polarity — occupation mass in the
goal window witnesses graph contact.  (Monotone former ∘ con
inclusion.) -/
theorem recordClass_dwell_subset_touch_deadline {τ : X → ℕ}
    {A : α → Set X} (n : ℕ) (φ : StateFormula α) (b : Bool) :
    recordCon ∩ recordClass .dwell τ A (.deadline n φ b)
      ⊆ recordClass .touch τ A (.deadline n φ b) := by
  rintro p ⟨hcon, h⟩
  exact windowReachOn_mono (recordCon_iff_stages.mp hcon) h

/-- **The until species are incomparable, even con-coupled** — both
non-inclusions witnessed on one two-stage lens point (full graph,
point mass on the late stage).  Until mixes the polarities: its target
conjunct is monotone in the occupied stages, its safety conjunct
antitone, so neither species transport survives.  The absence of an
until transport is content. -/
theorem exists_untilOn_species_incomparable :
    ∃ p ∈ recordCon (X := Bool),
      (untilOn (fun b => cond b 1 0) 1 ∅ {false} (stages .touch p) ∧
        ¬ untilOn (fun b => cond b 1 0) 1 ∅ {false} (stages .dwell p)) ∧
      (untilOn (fun b => cond b 1 0) 1 {true} {true} (stages .dwell p) ∧
        ¬ untilOn (fun b => cond b 1 0) 1 {true} {true}
          (stages .touch p)) := by
  classical
  refine ⟨(⟨⟨Set.univ, isCompact_univ⟩, ⟨false, Set.mem_univ _⟩⟩,
    ProbState.dirac true), fun x hx => Set.mem_univ x, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- touch-until reaches the early target with a vacuous safety window
    exact ⟨0, Nat.zero_le _,
      ⟨false, Set.mem_univ _, rfl, rfl⟩,
      fun x _ hlt => absurd hlt (Nat.not_lt_zero _)⟩
  · -- dwell-until fails: the support never occupies the target
    rintro ⟨t, -, ⟨x, hx, -, hxT⟩, -⟩
    have hxtrue : x = true := by
      by_contra hne
      exact hx (ProbState.dirac_apply_of_ne hne)
    rw [Set.mem_singleton_iff] at hxT
    exact Bool.noConfusion (hxtrue ▸ hxT)
  · -- dwell-until holds at the late tick, safety window vacuous on the
    -- support
    refine ⟨1, le_rfl, ⟨true, ?_, rfl, rfl⟩, fun x hx hlt => ?_⟩
    · show (ProbState.dirac true : Bool → ℝ) true ≠ 0
      rw [ProbState.dirac_apply_same]
      exact one_ne_zero
    · have hxtrue : x = true := by
        by_contra hne
        exact hx (ProbState.dirac_apply_of_ne hne)
      subst hxtrue
      exact absurd hlt (lt_irrefl _)
  · -- touch-until fails: the early stage is occupied and unsafe
    rintro ⟨t, ht, ⟨x, -, hτx, hxT⟩, hsafe⟩
    rw [Set.mem_singleton_iff] at hxT
    subst hxT
    -- the target witness pins the tick to 1
    have ht1 : t = 1 := by simpa using hτx.symm
    subst ht1
    have hf : false ∈ ({true} : Set Bool) :=
      hsafe false (Set.mem_univ _) (by simp)
    rw [Set.mem_singleton_iff] at hf
    exact Bool.noConfusion hf

/-- **The Streett species are incomparable, even con-coupled** — both
non-inclusions on the same lens point, one pair list each way.
Streett mixes the polarities inside a single pair: monotone in the
response occupation, antitone in the request occupation. -/
theorem exists_streettOn_species_incomparable :
    ∃ p ∈ recordCon (X := Bool),
      (streettOn [(({true} : Set Bool), ({false} : Set Bool))]
          (stages .touch p) ∧
        ¬ streettOn [(({true} : Set Bool), ({false} : Set Bool))]
          (stages .dwell p)) ∧
      (streettOn [(({false} : Set Bool), (∅ : Set Bool))]
          (stages .dwell p) ∧
        ¬ streettOn [(({false} : Set Bool), (∅ : Set Bool))]
          (stages .touch p)) := by
  classical
  refine ⟨(⟨⟨Set.univ, isCompact_univ⟩, ⟨false, Set.mem_univ _⟩⟩,
    ProbState.dirac true), fun x hx => Set.mem_univ x, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- touch answers: the graph occupies the response
    intro pr hpr
    rw [List.mem_singleton] at hpr
    subst hpr
    exact fun _ => ⟨false, Set.mem_univ _, rfl⟩
  · -- dwell cannot answer: the support occupies the request, not the
    -- response
    intro h
    obtain ⟨x, hx, hxresp⟩ := h ({true}, {false})
      (List.mem_singleton.mpr rfl)
      ⟨true, by
        show (ProbState.dirac true : Bool → ℝ) true ≠ 0
        rw [ProbState.dirac_apply_same]
        exact one_ne_zero, rfl⟩
    have hxtrue : x = true := by
      by_contra hne
      exact hx (ProbState.dirac_apply_of_ne hne)
    rw [Set.mem_singleton_iff] at hxresp
    exact Bool.noConfusion (hxtrue ▸ hxresp)
  · -- dwell holds vacuously: the support never requests
    intro pr hpr
    rw [List.mem_singleton] at hpr
    subst hpr
    rintro ⟨x, hx, hxreq⟩
    have hxtrue : x = true := by
      by_contra hne
      exact hx (ProbState.dirac_apply_of_ne hne)
    rw [Set.mem_singleton_iff] at hxreq
    exact Bool.noConfusion (hxtrue ▸ hxreq)
  · -- touch fails: the graph requests and nothing responds
    intro h
    obtain ⟨x, -, hx⟩ := h ({false}, ∅) (List.mem_singleton.mpr rfl)
      ⟨false, Set.mem_univ _, rfl⟩
    exact hx

/-! ### Citizenship: the factored topology lemmas, then the rows -/

/-- Containment demands on the occupied stages are closed, per
species: Vietoris on the graph face, coordinate equations on the
measure face. -/
theorem isClosed_stages_subset (sp : RecordSpecies) (C : Set X) :
    IsClosed {p : NonemptyCompacts X × ProbState X |
      stages sp p ⊆ C} := by
  classical
  cases sp with
  | touch =>
    rw [← isOpen_compl_iff]
    have heq : {p : NonemptyCompacts X × ProbState X |
        stages .touch p ⊆ C}ᶜ
        = {p : NonemptyCompacts X × ProbState X |
            ((p.1 : Set X) ∩ Cᶜ).Nonempty} := by
      ext p
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, stages_touch,
        Set.not_subset]
      constructor
      · rintro ⟨x, hxG, hxC⟩
        exact ⟨x, hxG, hxC⟩
      · rintro ⟨x, hxG, hxC⟩
        exact ⟨x, hxG, hxC⟩
    rw [heq]
    exact (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen
      (isOpen_discrete Cᶜ)).preimage continuous_fst
  | dwell =>
    have heq : {p : NonemptyCompacts X × ProbState X |
        stages .dwell p ⊆ C}
        = ⋂ x ∈ Cᶜ, {p : NonemptyCompacts X × ProbState X |
            (p.2 : X → ℝ) x = 0} := by
      ext p
      simp only [Set.mem_setOf_eq, stages_dwell, Set.mem_iInter,
        Set.mem_compl_iff]
      constructor
      · intro h x hxC
        by_contra hne
        exact hxC (h hne)
      · intro h x hne
        by_contra hxC
        exact hne (h x hxC)
    rw [heq]
    exact isClosed_biInter fun x _ => isClosed_eq
      (((continuous_apply x).comp continuous_subtype_val).comp
        continuous_snd) continuous_const

/-- Contact demands on the occupied stages are open, per species. -/
theorem isOpen_stages_inter_nonempty (sp : RecordSpecies) (B : Set X) :
    IsOpen {p : NonemptyCompacts X × ProbState X |
      (stages sp p ∩ B).Nonempty} := by
  classical
  cases sp with
  | touch =>
    exact (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen
      (isOpen_discrete B)).preimage continuous_fst
  | dwell =>
    have heq : {p : NonemptyCompacts X × ProbState X |
        (stages .dwell p ∩ B).Nonempty}
        = ⋃ x ∈ B, {p : NonemptyCompacts X × ProbState X |
            (p.2 : X → ℝ) x ≠ 0} := by
      ext p
      simp only [Set.mem_setOf_eq, stages_dwell, Set.mem_iUnion]
      constructor
      · rintro ⟨x, hx0, hxB⟩
        exact ⟨x, hxB, hx0⟩
      · rintro ⟨x, hxB, hx0⟩
        exact ⟨x, hx0, hxB⟩
    rw [heq]
    exact isOpen_biUnion fun x _ => isOpen_ne.preimage
      (((continuous_apply x).comp continuous_subtype_val).comp
        continuous_snd)

/-- Invariance classes are closed, both species. -/
theorem isClosed_recordClass_always (sp : RecordSpecies) (τ : X → ℕ)
    (A : α → Set X) (φ : StateFormula α) :
    IsClosed (recordClass sp τ A (.always φ)) :=
  isClosed_stages_subset sp (φ.den A)

/-- Bounded-invariance classes are closed, both species: the window
normal form is a containment demand. -/
theorem isClosed_recordClass_alwaysT (sp : RecordSpecies) (τ : X → ℕ)
    (A : α → Set X) (n : ℕ) (φ : StateFormula α) :
    IsClosed (recordClass sp τ A (.alwaysT n φ)) := by
  have heq : recordClass sp τ A (.alwaysT n φ)
      = {p : NonemptyCompacts X × ProbState X |
          stages sp p ⊆ φ.den A ∪ {x | n < τ x}} := by
    ext p
    exact windowAlwaysOn_iff_subset
  rw [heq]
  exact isClosed_stages_subset sp _

/-- Bounded-reach classes are open, both species: the window normal
form is a contact demand. -/
theorem isOpen_recordClass_deadline (sp : RecordSpecies) (τ : X → ℕ)
    (A : α → Set X) (n : ℕ) (φ : StateFormula α) (b : Bool) :
    IsOpen (recordClass sp τ A (.deadline n φ b)) := by
  have heq : recordClass sp τ A (.deadline n φ b)
      = {p : NonemptyCompacts X × ProbState X |
          (stages sp p ∩ (φ.den A ∩ {x | τ x ≤ n})).Nonempty} := by
    ext p
    exact windowReachOn_iff_inter
  rw [heq]
  exact isOpen_stages_inter_nonempty sp _

omit [DiscreteTopology X] in
/-- The window decomposition of the until class: finitely many tick
candidates, each a (contact demand) ∩ (containment demand) — an open
∩ closed piece per tick. -/
theorem recordClass_untilF_eq (sp : RecordSpecies) (τ : X → ℕ)
    (A : α → Set X) (n : ℕ) (sf tg : StateFormula α) :
    recordClass sp τ A (.untilF n sf tg)
      = ⋃ t : Fin (n + 1),
          ({p : NonemptyCompacts X × ProbState X |
              (stages sp p ∩ (tg.den A ∩ {x | τ x = (t : ℕ)})).Nonempty}
            ∩ {p : NonemptyCompacts X × ProbState X |
                stages sp p ⊆ sf.den A ∪ {x | ¬ τ x < (t : ℕ)}}) := by
  ext p
  rw [mem_recordClass_iff]
  show untilOn τ n (sf.den A) (tg.den A) (stages sp p) ↔ _
  rw [untilOn_iff_exists_fin]
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]

/-- **The until class is constructible, both species** — the grammar's
first genuinely constructible-not-closed-not-open record class: a
finite union of locally closed window pieces. -/
theorem isConstructibleUnion_recordClass_untilF (sp : RecordSpecies)
    (τ : X → ℕ) (A : α → Set X) (n : ℕ) (sf tg : StateFormula α) :
    IsConstructibleUnion (recordClass sp τ A (.untilF n sf tg)) := by
  rw [recordClass_untilF_eq]
  refine IsConstructibleUnion.iUnion_fin fun t => ?_
  exact IsLocallyClosed.isConstructibleUnion
    ((isOpen_stages_inter_nonempty sp _).isLocallyClosed.inter
      (isClosed_stages_subset sp _).isLocallyClosed)

/-- **The Streett class is constructible, both species**: each pair
contributes (no contact with the request) ∪ (contact with the
response) — a closed ∪ open factor — and the class is the finite
intersection of the factors. -/
theorem isConstructibleUnion_recordClass_streett (sp : RecordSpecies)
    (τ : X → ℕ) (A : α → Set X) (prs : List (StreettPair α)) :
    IsConstructibleUnion (recordClass sp τ A (.streett prs)) := by
  classical
  induction prs with
  | nil =>
    have heq : recordClass sp τ A (.streett ([] : List (StreettPair α)))
        = Set.univ := by
      ext p
      simp only [mem_recordClass_iff, Set.mem_univ, iff_true]
      exact streettOn_nil
    rw [heq]
    exact IsLocallyClosed.isConstructibleUnion
      isOpen_univ.isLocallyClosed
  | cons pr rest ih =>
    have heq : recordClass sp τ A (.streett (pr :: rest))
        = ({p : NonemptyCompacts X × ProbState X |
              (stages sp p ∩ pr.reqRegion A).Nonempty}ᶜ
            ∪ {p : NonemptyCompacts X × ProbState X |
                (stages sp p ∩ pr.respRegion A).Nonempty})
          ∩ recordClass sp τ A (.streett rest) := by
      ext p
      show streettOn _ _ ↔ _
      rw [List.map_cons, streettOn_cons]
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
        Set.mem_setOf_eq, mem_recordClass_iff]
      constructor
      · rintro ⟨hhd, htl⟩
        refine ⟨?_, htl⟩
        by_cases hreq : (stages sp p ∩ pr.reqRegion A).Nonempty
        · obtain ⟨x, hx, hresp⟩ := hhd (by
            obtain ⟨y, hyS, hyR⟩ := hreq
            exact ⟨y, hyS, hyR⟩)
          exact Or.inr ⟨x, hx, hresp⟩
        · exact Or.inl hreq
      · rintro ⟨hhd, htl⟩
        refine ⟨fun hreq => ?_, htl⟩
        rcases hhd with hno | ⟨x, hx, hresp⟩
        · obtain ⟨y, hyS, hyR⟩ := hreq
          exact absurd ⟨y, hyS, hyR⟩ hno
        · exact ⟨x, hx, hresp⟩
    rw [heq]
    refine IsConstructibleUnion.inter ?_ ih
    exact IsConstructibleUnion.union
      (IsLocallyClosed.isConstructibleUnion
        (isOpen_stages_inter_nonempty sp
          (pr.reqRegion A)).isClosed_compl.isLocallyClosed)
      (IsLocallyClosed.isConstructibleUnion
        (isOpen_stages_inter_nonempty sp
          (pr.respRegion A)).isLocallyClosed)

/-- **The compiled record atom is a citizen** (specimen: a bounded
invariance floor with a bounded reach goal): closed class + generic
wall lemma give the lsc floor; open class + generic mark lemma give
lsc marks. -/
theorem pathAtom_record_citizen (sp : RecordSpecies) (τ : X → ℕ)
    (A : α → Set X) (n m : ℕ) (φ ψ : StateFormula α) (b : Bool) :
    LowerSemicontinuous
        (pathAtom (recordClass sp τ A (.alwaysT n φ))
          (recordClass sp τ A (.deadline m ψ b))).floor ∧
      ∀ v ∈ (pathAtom (recordClass sp τ A (.alwaysT n φ))
          (recordClass sp τ A (.deadline m ψ b))).marks,
        LowerSemicontinuous v := by
  constructor
  · rw [pathAtom_floor]
    exact lowerSemicontinuous_wallOn_of_isClosed
      (isClosed_recordClass_alwaysT sp τ A n φ)
  · rintro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · exact lowerSemicontinuous_markOn_of_isOpen
        (isOpen_recordClass_deadline sp τ A m ψ b)
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      intro p y hy
      filter_upwards with q
      exact hy.trans_le le_top

end RecordClasses

/-! ## The species transports at the continuum stratum

The narrow-lens twins of the finitary transports, on the landed
continuum walls: con transports the graph-face invariance verdict to
the measure face, and occupation mass in a goal to graph contact.
No measurability of the region is needed — the graph's own
measurability carries both. -/

section Continuum

variable {X : Type*} [MeasurableSpace X] [MetricSpace X]
  [CompactSpace X] [BorelSpace X]

open MeasureTheory

/-- Invariance transports at narrow: a con-coupled pair whose graph
misses the bad region gives it no occupation mass. -/
theorem dwellWallNarrow_eq_zero_of_touchWallNarrow
    {p : NonemptyCompacts X × ProbabilityMeasure X} {Bad : Set X}
    (hcon : p ∈ narrowCon X) (h : touchWallNarrow Bad p = 0) :
    dwellWallNarrow Bad p = 0 := by
  classical
  have hmiss : ¬ ((p.1 : Set X) ∩ Bad).Nonempty := by
    intro hne
    rw [touchWallNarrow, if_pos hne] at h
    exact ENNReal.top_ne_zero h
  have hGmeas : MeasurableSet (p.1 : Set X) :=
    p.1.isCompact.isClosed.measurableSet
  have hsub : Bad ⊆ ((p.1 : Set X))ᶜ := by
    intro x hxB hxG
    exact hmiss ⟨x, hxG, hxB⟩
  have hcompl : (p.2 : Measure X) ((p.1 : Set X))ᶜ = 0 := by
    rw [measure_compl hGmeas (measure_ne_top _ _), measure_univ,
      mem_narrowCon_iff.mp hcon, tsub_self]
  have hzero : (p.2 : Measure X) Bad = 0 :=
    le_antisymm (le_of_le_of_eq (measure_mono hsub) hcompl) zero_le
  rw [dwellWallNarrow, if_neg]
  rw [hzero]
  exact lt_irrefl 0

/-- Reach transports at narrow, polarity flipped: occupation mass in a
goal region witnesses graph contact for a con-coupled pair. -/
theorem narrow_touch_of_dwell
    {p : NonemptyCompacts X × ProbabilityMeasure X} {Goal : Set X}
    (hcon : p ∈ narrowCon X) (h : 0 < (p.2 : Measure X) Goal) :
    ((p.1 : Set X) ∩ Goal).Nonempty := by
  by_contra hmiss
  have hGmeas : MeasurableSet (p.1 : Set X) :=
    p.1.isCompact.isClosed.measurableSet
  have hsub : Goal ⊆ ((p.1 : Set X))ᶜ := by
    intro x hxG hxGr
    exact hmiss ⟨x, hxGr, hxG⟩
  have hcompl : (p.2 : Measure X) ((p.1 : Set X))ᶜ = 0 := by
    rw [measure_compl hGmeas (measure_ne_top _ _), measure_univ,
      mem_narrowCon_iff.mp hcon, tsub_self]
  exact absurd (le_of_le_of_eq (measure_mono hsub) hcompl)
    (not_le.mpr h)

end Continuum

/-! ## The judgment squares at the lens carrier

Polarity dictates the face, the face dictates the direction: bounded
invariance enters on the safety floor and its horizon square points
long-to-short; bounded reach enters on the liveness marks and its
horizon square points short-to-long.  The species squares relativize
the con transport to lens-conformant systems.  All `sound` only. -/

section JudgmentSquares

variable {X : Type u} [Fintype X] [TopologicalSpace X] {α : Type v}

/-- The bounded-invariance safety square, horizon face: certify the
longer window, conclude every shorter claim. -/
theorem safetyAtom_alwaysT_anti_horizon (sp : RecordSpecies)
    (τ : X → ℕ) (A : α → Set X) {n n' : ℕ} (hn : n ≤ n')
    (φ : StateFormula α) :
    (safetyAtom (recordClass sp τ A (.alwaysT n' φ))).modelClass
      ⊆ (safetyAtom (recordClass sp τ A (.alwaysT n φ))).modelClass :=
  safetyAtom_modelClass_mono fun _ hp =>
    windowAlwaysOn_anti_window hn hp

/-- The bounded-reach liveness square, horizon face: the direction
REVERSES against the invariance square — certify the shorter deadline,
conclude every longer claim. -/
theorem pathAtom_deadline_mono_horizon (sp : RecordSpecies)
    (τ : X → ℕ) (A : α → Set X) {n n' : ℕ} (hn : n ≤ n')
    (φ : StateFormula α) (b : Bool) :
    (pathAtom Set.univ
        (recordClass sp τ A (.deadline n φ b))).modelClass
      ⊆ (pathAtom Set.univ
          (recordClass sp τ A (.deadline n' φ b))).modelClass :=
  pathAtom_modelClass_mono subset_rfl fun _ hp =>
    windowReachOn_mono_window hn hp

variable [DiscreteTopology X]

/-- The species square, safety polarity: for a lens-conformant system
(every permitted record con-coupled), the touch-certified bounded
invariance transports to the dwell claim. -/
theorem safetyAtom_alwaysT_touch_to_dwell (τ : X → ℕ) (A : α → Set X)
    (n : ℕ) (φ : StateFormula α)
    {σ : NonemptyCompacts X × ProbState X → ℝ≥0∞}
    (hσ : permitted σ ⊆ recordCon)
    (h : σ ∈ (safetyAtom
      (recordClass .touch τ A (.alwaysT n φ))).modelClass) :
    σ ∈ (safetyAtom
      (recordClass .dwell τ A (.alwaysT n φ))).modelClass := by
  rw [safetyAtom_modelClass, ← safeLive_univ_right] at h ⊢
  exact safeLive_mono_on hσ
    (recordClass_touch_subset_dwell_alwaysT n φ)
    (fun p _ => Set.mem_univ p) h

/-- The species square, liveness polarity: for a lens-conformant
system, the dwell-certified bounded reach transports to the touch
claim — the flip again, now at the judgment. -/
theorem pathAtom_deadline_dwell_to_touch (τ : X → ℕ) (A : α → Set X)
    (n : ℕ) (φ : StateFormula α) (b : Bool)
    {σ : NonemptyCompacts X × ProbState X → ℝ≥0∞}
    (hσ : permitted σ ⊆ recordCon)
    (h : σ ∈ (pathAtom Set.univ
      (recordClass .dwell τ A (.deadline n φ b))).modelClass) :
    σ ∈ (pathAtom Set.univ
      (recordClass .touch τ A (.deadline n φ b))).modelClass := by
  rw [pathAtom_modelClass] at h ⊢
  exact safeLive_mono_on hσ (fun p hp => Set.mem_univ p)
    (recordClass_dwell_subset_touch_deadline n φ b) h

end JudgmentSquares

/-! ## The deterministic bridge

A trajectory over the tick grid — a section of the tick coordinate,
restricted to a finite window — embeds in the lens as its stage graph
with the uniform lift.  There the species collapse, and each
combinator agrees with the specification catalogue's trajectory
semantics on the nose: the exact deterministic cells of the path
formers.  (The Streett clause reads the finite-record occupation
shadow; its infinitary acceptance lives at the behavioral tier, and
the pasting between the two is deliberately not claimed — the
`SpecBehavioral` fence.) -/

section Bridge

variable {X : Type u}

/-- The occupied stages of a trajectory over the window `0..N`. -/
def trajStages (w : ℕ → X) (N : ℕ) : Set X := w '' Set.Iic N

variable [Fintype X] [TopologicalSpace X] [DiscreteTopology X]

/-- The stage graph of a trajectory: a nonempty compact of the
finitary site. -/
def trajGraph (w : ℕ → X) (N : ℕ) : NonemptyCompacts X :=
  ⟨⟨trajStages w N, (Set.toFinite _).isCompact⟩,
    ⟨w 0, Set.mem_image_of_mem w (Set.mem_Iic.mpr (Nat.zero_le N))⟩⟩

omit [DiscreteTopology X] in
@[simp] theorem trajGraph_coe (w : ℕ → X) (N : ℕ) :
    (trajGraph w N : Set X) = trajStages w N := rfl

/-- The canonical lens point of a trajectory: its graph, uniformly
lifted. -/
noncomputable def trajLens (w : ℕ → X) (N : ℕ) :
    NonemptyCompacts X × ProbState X :=
  (trajGraph w N, uniformLift (trajGraph w N))

/-- Both species read a trajectory's lens point as its occupied
stages. -/
theorem stages_trajLens (sp : RecordSpecies) (w : ℕ → X) (N : ℕ) :
    stages sp (trajLens w N) = trajStages w N :=
  stages_uniformLift sp (trajGraph w N)

/-- A trajectory's lens point is con-coupled. -/
theorem trajLens_mem_recordCon (w : ℕ → X) (N : ℕ) :
    trajLens w N ∈ recordCon :=
  uniformLift_mem_recordCon (trajGraph w N)

variable {τ : X → ℕ} {w : ℕ → X} {N : ℕ}

omit [Fintype X] [TopologicalSpace X] [DiscreteTopology X] in
/-- Invariance at the trajectory: the catalogue's clause. -/
theorem alwaysOn_trajStages_iff {Good : Set X} :
    alwaysOn Good (trajStages w N) ↔ ∀ t ≤ N, w t ∈ Good := by
  constructor
  · intro h t ht
    exact h (Set.mem_image_of_mem w (Set.mem_Iic.mpr ht))
  · rintro h x ⟨t, ht, rfl⟩
    exact h t (Set.mem_Iic.mp ht)

omit [Fintype X] [TopologicalSpace X] [DiscreteTopology X] in
/-- Bounded invariance at the trajectory: the catalogue's clause,
under the section hypothesis on the tick coordinate. -/
theorem windowAlwaysOn_trajStages_iff (hw : ∀ t, τ (w t) = t)
    {n : ℕ} {Good : Set X} :
    windowAlwaysOn τ n Good (trajStages w N)
      ↔ ∀ t ≤ N, t ≤ n → w t ∈ Good := by
  constructor
  · intro h t htN htn
    exact h (w t) (Set.mem_image_of_mem w (Set.mem_Iic.mpr htN))
      (by rw [hw]; exact htn)
  · rintro h x ⟨t, ht, rfl⟩ hτ
    exact h t (Set.mem_Iic.mp ht) (by rwa [hw] at hτ)

omit [Fintype X] [TopologicalSpace X] [DiscreteTopology X] in
/-- Bounded reach at the trajectory: the catalogue's clause. -/
theorem windowReachOn_trajStages_iff (hw : ∀ t, τ (w t) = t)
    {n : ℕ} {Goal : Set X} :
    windowReachOn τ n Goal (trajStages w N)
      ↔ ∃ t ≤ N, t ≤ n ∧ w t ∈ Goal := by
  constructor
  · rintro ⟨x, ⟨t, ht, rfl⟩, hτ, hG⟩
    exact ⟨t, Set.mem_Iic.mp ht, by rwa [hw] at hτ, hG⟩
  · rintro ⟨t, htN, htn, hG⟩
    exact ⟨w t, Set.mem_image_of_mem w (Set.mem_Iic.mpr htN),
      by rw [hw]; exact htn, hG⟩

omit [Fintype X] [TopologicalSpace X] [DiscreteTopology X] in
/-- Until at the trajectory: the catalogue's clause — target by the
deadline, safety **strictly** before. -/
theorem untilOn_trajStages_iff (hw : ∀ t, τ (w t) = t)
    {n : ℕ} {Safe Target : Set X} :
    untilOn τ n Safe Target (trajStages w N)
      ↔ ∃ t, t ≤ n ∧ t ≤ N ∧ w t ∈ Target ∧
          ∀ s < t, w s ∈ Safe := by
  constructor
  · rintro ⟨t, htn, ⟨x, ⟨t', ht', rfl⟩, hτ, hT⟩, hsafe⟩
    rw [hw] at hτ
    subst hτ
    refine ⟨t', htn, Set.mem_Iic.mp ht', hT, fun s hs => ?_⟩
    refine hsafe (w s)
      (Set.mem_image_of_mem w (Set.mem_Iic.mpr
        (le_trans hs.le (Set.mem_Iic.mp ht')))) ?_
    rw [hw]
    exact hs
  · rintro ⟨t, htn, htN, hT, hsafe⟩
    refine ⟨t, htn,
      ⟨w t, Set.mem_image_of_mem w (Set.mem_Iic.mpr htN), hw t, hT⟩,
      ?_⟩
    rintro x ⟨s, hs, rfl⟩ hτ
    rw [hw] at hτ
    exact hsafe s hτ

variable {α : Type v}

/-- **The deterministic collapse of the compile**: a trajectory's lens
point is in a former's record class independently of the species, and
membership reads the occupied stages directly.  With the combinator
bridges above, the compile agrees with the catalogue's trajectory
semantics on the nose at every deterministic record. -/
theorem trajLens_mem_recordClass_iff {sp : RecordSpecies}
    {A : α → Set X} {ψ : PathNnf α} :
    trajLens w N ∈ recordClass sp τ A ψ
      ↔ recordPred τ A ψ (trajStages w N) := by
  rw [mem_recordClass_iff, stages_trajLens]

end Bridge

end SuFunctor.Universe

/-! ## Axiom receipts

Expected closure for every statement below: ⊆ `[propext,
Classical.choice, Quot.sound]`, zero `sorryAx`. -/

#print axioms SuFunctor.Universe.markOn_univ
#print axioms SuFunctor.Universe.dip_markOn_iff
#print axioms SuFunctor.Universe.coupledSat_pathAtom_iff
#print axioms SuFunctor.Universe.pathAtom_modelClass
#print axioms SuFunctor.Universe.safeLive_univ_right
#print axioms SuFunctor.Universe.pathAtom_univ_modelClass
#print axioms SuFunctor.Universe.pathAtom_modelClass_mono
#print axioms SuFunctor.Universe.safeLive_mono_on
#print axioms SuFunctor.Universe.lowerSemicontinuous_wallOn_of_isClosed
#print axioms SuFunctor.Universe.lowerSemicontinuous_markOn_of_isOpen
#print axioms SuFunctor.Universe.streettOn_mono
#print axioms SuFunctor.Universe.untilOn_univ_safe
#print axioms SuFunctor.Universe.not_windowAlwaysOn_iff
#print axioms SuFunctor.Universe.not_windowReachOn_iff
#print axioms SuFunctor.Universe.not_alwaysOn_iff
#print axioms SuFunctor.Universe.untilOn_iff_exists_fin
#print axioms SuFunctor.Universe.pathNnfAux_exact
#print axioms SuFunctor.Universe.pathNnf_exact
#print axioms SuFunctor.Universe.pathNnf_notPath_always
#print axioms SuFunctor.Universe.pathNnf_notPath_untilF
#print axioms SuFunctor.Universe.pathNnf_notPath_streett
#print axioms SuFunctor.Universe.pathNnf_notPath_alwaysT
#print axioms SuFunctor.Universe.recordCon_iff_stages
#print axioms SuFunctor.Universe.stages_uniformLift
#print axioms SuFunctor.Universe.touchWall_eq_wallOn
#print axioms SuFunctor.Universe.dwellWall_eq_wallOn
#print axioms SuFunctor.Universe.recordClass_touch_subset_dwell_always
#print axioms SuFunctor.Universe.recordClass_touch_subset_dwell_alwaysT
#print axioms SuFunctor.Universe.recordClass_dwell_subset_touch_deadline
#print axioms SuFunctor.Universe.exists_untilOn_species_incomparable
#print axioms SuFunctor.Universe.exists_streettOn_species_incomparable
#print axioms SuFunctor.Universe.isClosed_recordClass_always
#print axioms SuFunctor.Universe.isClosed_recordClass_alwaysT
#print axioms SuFunctor.Universe.isOpen_recordClass_deadline
#print axioms SuFunctor.Universe.isConstructibleUnion_recordClass_untilF
#print axioms SuFunctor.Universe.isConstructibleUnion_recordClass_streett
#print axioms SuFunctor.Universe.pathAtom_record_citizen
#print axioms SuFunctor.Universe.dwellWallNarrow_eq_zero_of_touchWallNarrow
#print axioms SuFunctor.Universe.narrow_touch_of_dwell
#print axioms SuFunctor.Universe.safetyAtom_alwaysT_anti_horizon
#print axioms SuFunctor.Universe.pathAtom_deadline_mono_horizon
#print axioms SuFunctor.Universe.safetyAtom_alwaysT_touch_to_dwell
#print axioms SuFunctor.Universe.pathAtom_deadline_dwell_to_touch
#print axioms SuFunctor.Universe.trajLens_mem_recordCon
#print axioms SuFunctor.Universe.alwaysOn_trajStages_iff
#print axioms SuFunctor.Universe.windowAlwaysOn_trajStages_iff
#print axioms SuFunctor.Universe.windowReachOn_trajStages_iff
#print axioms SuFunctor.Universe.untilOn_trajStages_iff
#print axioms SuFunctor.Universe.trajLens_mem_recordClass_iff
