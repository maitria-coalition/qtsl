/-
RETIRED (archived).  This module belongs to the retired calculus-side
semantic tier, whose target is the thin double category of per-element
constraints on finitely supported subprobability mass functions
(`SuFunctor.Crd`).  That tier is superseded by the sheaf-fibred
construction: the locally closed Fell-hyperspace universe
(`SuFunctor.Universe`), the plain spec-class decoration functor
(`SuFunctor.Plain.SpecFunctor`), and the site-dimensional functor
(`SuFunctor.Site.SiteFunctor`).

This module: the virtual-route semantic functor (`Deriv.sem`) into the
per-element stratum.  The virtual presentation of the source itself
(`SuFunctor.Virtual`) is not retired.

New results must not import this module.  A result still needed
against the current semantics should be restated over the successor
carrier rather than proven here.
-/
import SuFunctor.Virtual
import SuFunctorLegacy.Squares
import DoubleCat.Virtual.Functor
import DoubleCat.Virtual.OfPseudo

/-! # The semantic functor, virtually

The semantic reading of the virtual presentation: judgments map to their
satisfaction constraints, multicells map to multi-premise semantic
entailments, and the whole assembles into a functor of virtual double
categories from the proof calculus to (the underlying virtual double
category of) the per-element stratum of the denotation tier.

## What the virtual presentation changes semantically

(Historical references below are to the *retired kind-table*
presentation — the one-slot loose composition whose refutation
`SuFunctorLegacy.Refute` keeps as regression pins.  The repaired pseudo
presentation of `SuFunctorLegacy.Source` composes by formal conjunction and
owes none of the retired obligations; `SuFunctorLegacy.Transpose` proves it is
exactly the free promotion of this virtual one.)

* **`Deriv.sem` is unconditional.**  The kind-table presentation's
  semantic reading was conditional on the coherence bundle
  `SatCoherence`, which was refuted for every hypernet: the associator
  and congruence constructors of the derivation calculus demanded
  squares the table could not supply.  The virtual derivation calculus
  has no structure-cell constructors at all — substitution is the only
  closure, and substitution of entailments is just entailment
  composition — so the semantic reading holds outright.  (Under formal
  conjunction the bundle is instead *proven*, `satCoherence`; here the
  obligations are not even formulable, because no composite exists to
  constrain.)

* **Multi-premise rules enter with their pairs intact.**  The retired
  interface obstruction (a mixed-kind premise pair collapsed to the
  vacuous judgment through the kind table, so the sound two-premise
  safety-shell implication had a refuted family form) is dissolved
  rather than repaired: `safetyShellPair` below is `safetyShell` as a
  2-ary family square, verbatim.  (Formal conjunction dissolves it the
  same way — `SuFunctorLegacy.Squares.safetyBatteryFamily` — by retaining the
  pair as a list on the other side of the promotion.)

* **Cut is a 2-ary multicell.**  The cut countermodel (recorded in
  `SuFunctorLegacy.Refute`'s module docstring and the design record) shows
  cut's premise pair is strictly stronger than its conjunct composite,
  which is why the kind-table presentation had to keep cut inside the
  proof-object calculus.  Here `cutFamily` states cut at the judgment
  level with its two premises as a list, and `sat_cut` proves the
  satisfaction square: the violation event of the conclusion is
  contained in the union of the violation events of the premises, so
  zero upper mass on each premise forces zero upper mass on the
  conclusion.

* **The anchor is a nullary multicell.**  A checker theorem enters as a
  cell with empty loose domain (`Deriv.ofProof`); the unit judgment the
  kind-table presentation used as a top is not needed (under formal
  conjunction it is likewise a cell from the empty list), and
  `semVirtual_sound` re-derives the composed statement — a proof object
  asserts its sequent's judgment in every subprobability model (the
  premise list is empty, so the entailment is categorical), and the
  anchor equivalence converts that to the calculus's own semantic
  validity.
-/

namespace SuFunctor

namespace Virtual

open PPLC CategoryTheory

variable {H : Hypernet}

/-- Satisfaction of a list of judgments: the semantic reading of a
multicell's loose domain.  No composite judgment intervenes — the list
is read pointwise.  (This is definitionally `SatConj`, the loose action
of the formal-conjunction presentation's semantic functor; the two
presentations agree on loose semantics on the nose.) -/
def SatList (H : Hypernet) (js : List Judgment)
    (μ : SubPMF (AdmVal H)) : Prop :=
  ∀ j ∈ js, Sat H j μ

@[simp] theorem satList_nil (μ : SubPMF (AdmVal H)) :
    SatList H [] μ := fun _ hj => absurd hj (by simp)

theorem satList_cons {j : Judgment} {js : List Judgment}
    {μ : SubPMF (AdmVal H)} :
    SatList H (j :: js) μ ↔ Sat H j μ ∧ SatList H js μ := by
  constructor
  · exact fun h => ⟨h j (List.mem_cons_self ..),
      fun k hk => h k (List.mem_cons_of_mem j hk)⟩
  · rintro ⟨hj, hjs⟩ k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hj
    · exact hjs k hk

/-- A rule family together with its semantic squares, multi-ary form:
one square per enabled instance, with the premises entering as a list
rather than through a loose composite. -/
structure SemRuleFamily (H : Hypernet) : Type 1 where
  /-- The syntactic family. -/
  rules : RuleFamily H
  /-- One semantic square per enabled instance. -/
  square : ∀ t, rules.gate t → ∀ μ : SubPMF (AdmVal H),
    SatList H (rules.tops t) μ → Sat H (rules.bot t) μ

/-- **The semantic reading of a virtual derivation** — unconditional.
Structural recursion: family generators map to their squares, proof
objects to the anchor square, identities to identities, and splicing to
composition of entailments.  No coherence bundle enters: the virtual
presentation has no structure cells to interpret.  (The
formal-conjunction presentation's reading, `JDeriv.sem`, instead
consumes the proven `satCoherence` at its structure-cell cases.) -/
theorem Deriv.sem {F : RuleFamily H}
    (sq : ∀ t, F.gate t → ∀ μ : SubPMF (AdmVal H),
      SatList H (F.tops t) μ → Sat H (F.bot t) μ)
    {ps : List Judgment} {q : Judgment} (d : Deriv H F ps q) :
    ∀ μ : SubPMF (AdmVal H), SatList H ps μ → Sat H q μ := by
  induction d with
  | ofRule t ht => exact sq t ht
  | ofProof po => exact fun μ _ => sat_ofProof po μ
  | refl j => exact fun μ h => h j (List.mem_cons_self ..)
  | @splice as cs ps' b r _ _ ihmain ihinner =>
      intro μ h
      apply ihmain μ
      intro j hj
      rcases List.mem_append.mp hj with hja | hjbc
      · exact h j (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hja))))
      · rcases List.mem_cons.mp hjbc with rfl | hjc
        · exact ihinner μ fun k hk =>
            h k (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hk))))
        · exact h j (List.mem_append.mpr (Or.inr hjc))

/-! ## The square inventory, multi-ary -/

/-- A proved family of the formal-conjunction presentation lifts
blockwise: one virtual rule instance per member of the conclusion list,
with the premise list carried over verbatim.  (This is how the
`SuFunctor.SemRuleFamily` inventory — the transport families, the
demoted table rows, the pair-retention witnesses — enters the virtual
presentation: nothing about the premises changes, and a multi-judgment
conclusion becomes one multicell per member.) -/
def ofConj (F : SuFunctor.SemRuleFamily H) : SemRuleFamily H where
  rules :=
    { Tag := Σ t : F.rules.Tag, { j : Judgment // j ∈ F.rules.bot t }
      gate := fun i => F.rules.gate i.1
      tops := fun i => F.rules.top i.1
      bot := fun i => i.2.1 }
  square := fun i hi μ h => F.square i.1 hi μ h i.2.1 i.2.2

/-- The coproduct of two semantic families: tags are summed, squares
dispatch.  Families assemble monoidally, so the worked instances below
combine into a single family when convenient. -/
def SemRuleFamily.sum (F G : SemRuleFamily H) : SemRuleFamily H where
  rules :=
    { Tag := F.rules.Tag ⊕ G.rules.Tag
      gate := Sum.elim F.rules.gate G.rules.gate
      tops := Sum.elim F.rules.tops G.rules.tops
      bot := Sum.elim F.rules.bot G.rules.bot }
  square := by
    rintro (t | t) ht μ h
    · exact F.square t ht μ h
    · exact G.square t ht μ h

/-- **Cut, as a 2-ary rule family.**  Instances are triples
`(Φ, χ, Ψ)`; the premises `Φ ⊢ χ` and `Φ ∧ χ ⊢ Ψ` enter as a list — the
pair the retired conjunct composite provably forgot — and the gate is
trivial: cut is unconditional.  The square is the satisfaction argument:
a valuation violating `Φ ⊢ Ψ` either fails `χ` (violating the first
premise) or satisfies it (violating the second), so the conclusion's
violation event is contained in the union of the premises', and zero
upper mass on each forces zero on the conclusion. -/
def cutFamily (H : Hypernet) : SemRuleFamily H where
  rules :=
    { Tag := Formula × Formula × Formula
      gate := fun _ => True
      tops := fun i =>
        [.seqValid ⟨i.1, i.2.1⟩, .seqValid ⟨.and i.1 i.2.1, i.2.2⟩]
      bot := fun i => .seqValid ⟨i.1, i.2.2⟩ }
  square := by
    rintro ⟨φ, χ, ψ⟩ - μ h
    have h₁ : μ.prob (violation H ⟨φ, χ⟩) ≤ 0 :=
      h _ (List.mem_cons_self ..)
    have h₂ : μ.prob (violation H ⟨.and φ χ, ψ⟩) ≤ 0 :=
      h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    show μ.prob (violation H ⟨φ, ψ⟩) ≤ 0
    have hsub : violation H ⟨φ, ψ⟩ ⊆
        violation H ⟨φ, χ⟩ ∪ violation H ⟨.and φ χ, ψ⟩ := by
      rintro σ ⟨hpre, hnpost⟩
      by_cases hχ : χ.holds σ.1
      · exact Or.inr ⟨⟨hpre, hχ⟩, hnpost⟩
      · exact Or.inl ⟨hpre, hχ⟩
    have hu := le_trans (μ.prob_mono hsub)
      (μ.prob_union_le (violation H ⟨φ, χ⟩) (violation H ⟨.and φ χ, ψ⟩))
    have h0 := μ.prob_nonneg (violation H ⟨φ, ψ⟩)
    linarith

/-- **Cut as a multicell**: the 2-ary derivability cell, an ordinary
generator of the virtual presentation.  In the retired kind-table
presentation this boundary was not expressible — a cell's loose top was
a single judgment, and the composite of cut's premises is strictly
weaker than the pair.  (The formal-conjunction presentation expresses
it as a cell out of the two-element list, `SuFunctorLegacy.Squares.cutFamily`;
the two are the same cell across the free promotion.) -/
theorem cut_multicell (φ χ ψ : Formula) :
    Deriv H (cutFamily H).rules
      [.seqValid ⟨φ, χ⟩, .seqValid ⟨.and φ χ, ψ⟩]
      (.seqValid ⟨φ, ψ⟩) :=
  Deriv.ofRule (F := (cutFamily H).rules) (φ, χ, ψ) trivial

/-- **The satisfaction square for cut**, stated on the premise pair: any
subprobability model satisfying both premise judgments satisfies the
conclusion judgment.  This is the square the retired kind-table
presentation structurally could not state (its family interface routed
premises through the one-slot composite, and `(Φ ⊢ χ) ⊙ (Φ∧χ ⊢ Ψ)`
forgot the pair); here it is `cutFamily`'s square at a singleton
instance. -/
theorem sat_cut (φ χ ψ : Formula) (μ : SubPMF (AdmVal H))
    (h₁ : Sat H (.seqValid ⟨φ, χ⟩) μ)
    (h₂ : Sat H (.seqValid ⟨.and φ χ, ψ⟩) μ) :
    Sat H (.seqValid ⟨φ, ψ⟩) μ := by
  refine (cutFamily H).square (φ, χ, ψ) trivial μ ?_
  intro j hj
  rcases List.mem_cons.mp hj with rfl | hj
  · exact h₁
  · rcases List.mem_cons.mp hj with rfl | hj
    · exact h₂
    · exact absurd hj (by simp)

/-- **The union bound with its premise pair intact**: two risk bounds
enter as a 2-ary top.  (The retired kind-table presentation routed them
through the Boole composite first; the repaired `unionBoundFamily`
retains the pair as a two-element list, so on this rule the two repaired
presentations agree verbatim across the promotion.)  The square is
Boole's inequality plus monotonicity, directly. -/
def unionBoundPair (H : Hypernet) : SemRuleFamily H where
  rules :=
    { Tag := ℚ × ℚ × Formula × Formula × Formula
      gate := fun i => evt H i.2.2.2.2 ⊆ evt H i.2.2.1 ∪ evt H i.2.2.2.1
      tops := fun i =>
        [.probLE i.1 i.2.2.1, .probLE i.2.1 i.2.2.2.1]
      bot := fun i => .probLE (i.1 + i.2.1) i.2.2.2.2 }
  square := by
    rintro ⟨a, b, e₁, e₂, fail⟩ hgate μ h
    have h₁ : μ.prob (evt H e₁) ≤ a := h _ (List.mem_cons_self ..)
    have h₂ : μ.prob (evt H e₂) ≤ b :=
      h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    show μ.prob (evt H fail) ≤ a + b
    have hu := μ.prob_union_le (evt H e₁) (evt H e₂)
    have hm := μ.prob_mono hgate
    linarith

/-- **The safety shell enters the family** — the retired interface
obstruction, dissolved.  `SuFunctorLegacy.Squares.safetyShell` proves the
two-premise implication (risk bound on the avoided region plus mass
totality yields the guarantee, under covering); the retired kind table
collapsed exactly this premise pair to the vacuous judgment, turning the
sound rule into the refuted `⊤ → probGE p φ` (the collapse is now a
type error, pinned in `SuFunctorLegacy.Refute`).  With list tops the proved
implication *is* the square, verbatim — here as a 2-ary multicell, and
in the formal-conjunction presentation as
`SuFunctorLegacy.Squares.safetyBatteryFamily`. -/
def safetyShellPair (H : Hypernet) : SemRuleFamily H where
  rules :=
    { Tag := ℚ × Formula × Formula
      gate := fun i => ∀ σ : AdmVal H, σ ∈ evt H i.2.1 ∪ evt H i.2.2
      tops := fun i => [.probLE (1 - i.1) i.2.2, .probGE 1 .tt]
      bot := fun i => .probGE i.1 i.2.1 }
  square := by
    rintro ⟨p, φG, U⟩ hcover μ h
    exact safetyShell H p φG U hcover μ
      (h _ (List.mem_cons_self ..))
      (h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

/-! ## The functor -/

open VirtualDoubleCategoryData VirtualDoubleCategoryStruct

/-- The target virtual double category: the underlying virtual double
category of the thin double category of per-element constraints. -/
noncomputable instance {V : Type} :
    VirtualDoubleCategoryStruct (Crd V) :=
  .ofPseudo

instance {V : Type} : VirtualDoubleCategory (Crd V) :=
  .of_subsingleton fun _ _ _ _ => inferInstanceAs (Subsingleton (PLift _))

/-- Folding a mapped string in the target computes pointwise
satisfaction of the underlying judgment list. -/
theorem foldMap_sat {F : RuleFamily H} :
    ∀ {a b : BLV H F} (ps : LoosePath Loose a b)
      (μ : SubPMF (AdmVal H)),
      ((ps.map (fun _ => Crd.mk') fun {_ _} j => Sat H j).fold) μ ↔
        SatList H (BLV.pathToList ps) μ
  | _, _, .nil, μ => by
      constructor
      · exact fun _ => satList_nil μ
      · exact fun _ => trivial
  | _, _, .cons j ps, μ => by
      rw [BLV.pathToList_cons, satList_cons]
      exact and_congr Iff.rfl (foldMap_sat ps μ)

/-- **The semantic functor of virtual double categories**: judgments map
to their satisfaction constraints, multicells to multi-premise semantic
entailments (`Deriv.sem`).  Unconditional, with no coherence bundle
anywhere in its assembly.  The preservation laws hold by proof
irrelevance in the thin target (`VirtualDoubleFunctor.ofThin`). -/
noncomputable def semVirtualFunctor (H : Hypernet) (F : SemRuleFamily H) :
    VirtualDoubleFunctor (BLV H F.rules) (Crd (AdmVal H)) :=
  .ofThin
    (fun _ _ _ _ => inferInstanceAs (Subsingleton (PLift _)))
    { obj := fun _ => Crd.mk'
      map := fun _ => ⟨⟩ }
    (fun {_ _} j => Sat H j)
    (fun {_ _ _ _ ps q _ _} α =>
      ⟨fun μ hμ => Deriv.sem F.square α.down μ ((foldMap_sat ps μ).mp hμ)⟩)

/-- **The composed statement, through the virtual route**: a proof
object enters as a nullary multicell, its semantic reading asserts the
sequent's judgment in every subprobability model (the premise list is
empty, so the entailment is categorical), and the anchor equivalence
converts that to the calculus's own semantic validity.  The virtual
presentation preserves the composed-sentence gain — with no coherence
hypothesis anywhere in the path. -/
theorem semVirtual_sound (H : Hypernet) {seq : Sequent}
    (po : ProofObject H seq) : seq.semanticallyValid H :=
  (satAll_ofSequent_iff H seq).mp fun μ =>
    Deriv.sem (F := RuleFamily.empty H) (fun t => t.elim)
      (Deriv.ofProof po) μ (satList_nil μ)

end Virtual

end SuFunctor
