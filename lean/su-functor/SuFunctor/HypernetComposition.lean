import SuFunctor.HypernetInclusion

/-! # The composition calculus of the hypernet inclusion

`SuFunctor.HypernetInclusion` proves the transformation laws of the
possibilistic inclusion θ one composition at a time: `theta_comp` for a
single binary gluing, `theta_rename` for a single renaming cell,
`theta_unit` at a single interface.  This module states the *calculus*
those laws generate — the facts a composite of many components consumes
at once — at the same stratum: wire identity is content-addressed (one
ambient table `ty`, gluing by literal name-sharing, union apexes), the
stratum on which the aligned presentation is canonical.

## Main statements

* **Strictness of the stratum** (`AlignedLoose.seq_assoc`,
  `AlignedLoose.unit_seq`, `AlignedLoose.seq_unit`): composition of
  aligned interfaces is associative and unital *on the nose* — equality
  of structures, not isomorphism.  There is no coherence tower to pay on
  the content-addressed stratum, which is what licenses the triple-
  composition normal forms below.
* **Triple composition normalizes** (`theta_comp3_left`,
  `theta_comp3_right`, `austereDnf_assoc_heq`): both compositor routes
  through a threefold gluing land on the austere presentation of the
  flat data, and the two flat forms coincide along `seq_assoc`.  The
  θ-image lies in the strict locus of the semantic universe's laxity:
  reassociating a composite costs nothing, semantically.
* **Substitutability** (`austereDnf_subst`, via
  `admRegion_append_congr`): components with equal θ-images are
  interchangeable in any composite — composition respects semantic
  equivalence, so a certified interface claim about one presentation
  transfers to every extensionally equal presentation in every wiring
  context.  This is the congruence property that makes the composition
  patterns of the specification toolkit *patterns* rather than
  per-syntax accidents.
* **Infeasibility propagates** (`admRegion_append_empty_left`,
  `admRegion_append_empty_right`, `suppIn_admRegion_empty`): an
  infeasible component makes every composite containing it infeasible,
  and the infeasible composite denotes the bottom credal body — the
  zero-joint singleton (`SuFunctor.Plain.suppIn_empty`), never the empty
  set of beliefs.
* **The converse fails, witnessed** (`share_feasible`,
  `share_contradiction`): two feasible components sharing a wire can
  compose to an infeasible whole — two constant sources demanding
  different values of one shared variable.  Feasibility is *not*
  compositional, exactly where infeasibility is; the seam is where
  composites go infeasible, and the witness is the minimal instance of
  the variable-sharing pattern.
* **Naturality against the compositor** (`AlignedCell.seqCell`,
  `AlignedCell.restrictLeft`/`restrictRight`, `theta_rename_seq`,
  `compFst_splitTot_renameTot`, `compSnd_splitTot_renameTot`): renaming
  a composite is the composite of the renamings, both on θ-images (the
  hexagon closing `theta_comp` against `theta_rename`) and at the state
  level, where the square commutes *definitionally* — on the
  content-addressed stratum the split comparison has no moving parts to
  be natural *up to*.

The typing-side helper (`PPLC.PrimApp.TypeConsistent_congr`,
`TypeConsistent_tableOn_mono`) records that type consistency reads the
typing table only at an application's own wires, so consistency at a
component's apex transfers to every enclosing apex — the
hypothesis-plumbing every multi-component statement above consumes.
-/

namespace PPLC

/-- Type consistency reads the typing table only at an application's own
wires: tables agreeing there assign the same consistency.  (One
direction; the `Iff` form is `TypeConsistent_congr`.) -/
theorem PrimApp.TypeConsistent_of_congr {wt wt' : Wire → Option TensorType}
    (a : PrimApp)
    (h : ∀ w ∈ a.inputWires ++ a.outputWires, wt w = wt' w)
    (hTC : a.TypeConsistent wt) : a.TypeConsistent wt' := by
  have hIn : ∀ w ∈ a.inputWires, wt w = wt' w := fun w hw =>
    h w (List.mem_append_left _ hw)
  have hOut : ∀ w ∈ a.outputWires, wt w = wt' w := fun w hw =>
    h w (List.mem_append_right _ hw)
  cases a with
  | const ty c out =>
      have := hOut out (by simp [outputWires])
      simp only [TypeConsistent] at hTC ⊢
      rw [← this]; exact hTC
  | contract δ r inputs output inputRanks outputRank pat =>
      have hout := hOut output (by simp [outputWires])
      have hins : ∀ w ∈ inputs, wt w = wt' w := fun w hw =>
        hIn w (by simpa [inputWires] using hw)
      obtain ⟨hlen, h2, h3, h4, h5⟩ := hTC
      refine ⟨hlen, ?_, ?_, ?_, ?_⟩
      · intro p hp
        rw [← hins p.1 (List.of_mem_zip hp).1]; exact h2 p hp
      · rw [← hout]; exact h3
      · intro i a
        have hmem : inputs.getD i.val 0 ∈ inputs := by
          have hlt : i.val < inputs.length := by
            have := i.isLt; omega
          have heq : inputs.getD i.val 0 = inputs[i.val] := by
            simp [List.getD, List.getElem?_eq_getElem hlt]
          rw [heq]
          exact List.getElem_mem hlt
        rw [← hins _ hmem]; exact h4 i a
      · intro a; rw [← hout]; exact h5 a
  | cast δf δt r shape i o =>
      have hi := hIn i (by simp [inputWires])
      have ho := hOut o (by simp [outputWires])
      simp only [TypeConsistent] at hTC ⊢
      rw [← hi, ← ho]; exact hTC
  | cell schema i outs =>
      have hi := hIn i (by simp [inputWires])
      have houts : ∀ o ∈ outs, wt o = wt' o := fun o ho =>
        hOut o (by simpa [outputWires] using ho)
      obtain ⟨h1, h2, h3⟩ := hTC
      exact ⟨by rw [← hi]; exact h1, h2,
        fun o ho => by rw [← houts o ho]; exact h3 o ho⟩
  | reshape sh i o =>
      have hi := hIn i (by simp [inputWires])
      have ho := hOut o (by simp [outputWires])
      simp only [TypeConsistent] at hTC ⊢
      rw [← hi, ← ho]; exact hTC
  | broadcast sh i o =>
      have hi := hIn i (by simp [inputWires])
      have ho := hOut o (by simp [outputWires])
      simp only [TypeConsistent] at hTC ⊢
      rw [← hi, ← ho]; exact hTC
  | copy k i outs =>
      have hi := hIn i (by simp [inputWires])
      have houts : ∀ o ∈ outs, wt o = wt' o := fun o ho =>
        hOut o (by simpa [outputWires] using ho)
      obtain ⟨h1, τ, h2, h3⟩ := hTC
      exact ⟨h1, τ, by rw [← hi]; exact h2,
        fun o ho => by rw [← houts o ho]; exact h3 o ho⟩
  | delete i =>
      have hi := hIn i (by simp [inputWires])
      simp only [TypeConsistent] at hTC ⊢
      rw [← hi]; exact hTC
  | swap i1 i2 o1 o2 =>
      have h1 := hIn i1 (by simp [inputWires])
      have h2 := hIn i2 (by simp [inputWires])
      have h3 := hOut o1 (by simp [outputWires])
      have h4 := hOut o2 (by simp [outputWires])
      simp only [TypeConsistent] at hTC ⊢
      rw [← h1, ← h2, ← h3, ← h4]; exact hTC
  | relu sh i o =>
      have hi := hIn i (by simp [inputWires])
      have ho := hOut o (by simp [outputWires])
      simp only [TypeConsistent] at hTC ⊢
      rw [← hi, ← ho]; exact hTC
  | stack k sh ins o =>
      have ho := hOut o (by simp [outputWires])
      have hins : ∀ w ∈ ins, wt w = wt' w := fun w hw =>
        hIn w (by simpa [inputWires] using hw)
      obtain ⟨h1, τ, h2, h3, h4⟩ := hTC
      exact ⟨h1, τ, by rw [← ho]; exact h2, h3,
        fun w hw => by rw [← hins w hw]; exact h4 w hw⟩
  | ppoly n cf ins o =>
      have ho := hOut o (by simp [outputWires])
      have hins : ∀ w ∈ ins, wt w = wt' w := fun w hw =>
        hIn w (by simpa [inputWires] using hw)
      obtain ⟨h1, h2, h3⟩ := hTC
      exact ⟨h1, fun w hw => by rw [← hins w hw]; exact h2 w hw,
        by rw [← ho]; exact h3⟩
  | pderiv sh ax i o =>
      have hi := hIn i (by simp [inputWires])
      have ho := hOut o (by simp [outputWires])
      simp only [TypeConsistent] at hTC ⊢
      rw [← hi, ← ho]; exact hTC
  | facet sh ax hi' i o =>
      have hi := hIn i (by simp [inputWires])
      have ho := hOut o (by simp [outputWires])
      simp only [TypeConsistent] at hTC ⊢
      rw [← hi, ← ho]; exact hTC

/-- Type consistency depends on the typing table only at the
application's own wires. -/
theorem PrimApp.TypeConsistent_congr {wt wt' : Wire → Option TensorType}
    (a : PrimApp)
    (h : ∀ w ∈ a.inputWires ++ a.outputWires, wt w = wt' w) :
    a.TypeConsistent wt ↔ a.TypeConsistent wt' :=
  ⟨PrimApp.TypeConsistent_of_congr a h,
   PrimApp.TypeConsistent_of_congr a fun w hw => (h w hw).symm⟩

end PPLC

namespace SuFunctor

noncomputable section

open CategoryTheory CategoryTheory.WireSpan PPLC
open SuFunctor.Plain SuFunctor.Universe
open scoped NNReal ENNReal

variable (ty : Wire → Option TensorType)

variable {X Y Z V X' Y' Z' : Finset Wire}

/-- Consistency at a restriction table transfers to any larger roster's
restriction table, when the application's wires lie in the smaller
one. -/
theorem TypeConsistent_tableOn_mono {W W' : Finset Wire} (hsub : W ⊆ W')
    {a : PrimApp}
    (hw : ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ W)
    (hTC : a.TypeConsistent (tableOn ty W)) :
    a.TypeConsistent (tableOn ty W') :=
  (PrimApp.TypeConsistent_congr a fun w hww => by
    rw [tableOn_pos ty (hw w hww), tableOn_pos ty (hsub (hw w hww))]).mp hTC

/-! ## Strictness of the content-addressed stratum

Aligned looses are determined by their apexes (the leg fields are
propositional), so the union calculus of `Finset` makes their
composition a strict monoid-like structure: associative and unital on
the nose.  No coherence tower exists to be paid. -/

/-- Aligned looses with equal apexes are equal. -/
theorem AlignedLoose.ext_apex {m m' : AlignedLoose X Y}
    (h : m.apex = m'.apex) : m = m' := by
  cases m; cases m'; cases h; rfl

/-- Composition of aligned looses is associative on the nose. -/
theorem AlignedLoose.seq_assoc (m : AlignedLoose X Y) (n : AlignedLoose Y Z)
    (p : AlignedLoose Z V) : (m.seq n).seq p = m.seq (n.seq p) :=
  AlignedLoose.ext_apex (Finset.union_assoc _ _ _)

/-- The loose identity is a strict left unit. -/
theorem AlignedLoose.unit_seq (m : AlignedLoose X Y) :
    (AlignedLoose.unit X).seq m = m :=
  AlignedLoose.ext_apex (Finset.union_eq_right.mpr m.left_le)

/-- The loose identity is a strict right unit. -/
theorem AlignedLoose.seq_unit (m : AlignedLoose X Y) :
    m.seq (AlignedLoose.unit Y) = m :=
  AlignedLoose.ext_apex (Finset.union_eq_left.mpr m.right_le)

/-- The austere presentation respects equality of its aligned data,
heterogeneously (the carrier type follows the apex). -/
theorem austereDnf_congr_heq {m m' : AlignedLoose X Y} (hm : m = m')
    {T T' : List PrimApp} (hT : T = T') :
    austereDnf ty m T ≍ austereDnf ty m' T' := by
  subst hm; subst hT; rfl

/-! ## Triple composition normalizes

Both compositor routes through a threefold gluing land on the austere
presentation of the flat data; the two flat forms coincide along
`seq_assoc`.  The θ-image lies in the strict locus of the semantic
universe's laxity. -/

/-- Left-nested route: composing the first two components, then the
third, normalizes to the flat austere presentation. -/
theorem theta_comp3_left (m : AlignedLoose X Y) (n : AlignedLoose Y Z)
    (p : AlignedLoose Z V) (T₁ T₂ T₃ : List PrimApp)
    (hTC₁ : ∀ a ∈ T₁, a.TypeConsistent (tableOn ty m.apex))
    (hw₁ : ∀ a ∈ T₁, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ m.apex)
    (hTC₂ : ∀ a ∈ T₂, a.TypeConsistent (tableOn ty n.apex))
    (hw₂ : ∀ a ∈ T₂, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ n.apex)
    (hTC₃ : ∀ a ∈ T₃, a.TypeConsistent (tableOn ty p.apex))
    (hw₃ : ∀ a ∈ T₃, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ p.apex) :
    dnfPull (splitTot ty (m.seq n) p)
        (dnfBoxplus
          (dnfPull (splitTot ty m n)
            (dnfBoxplus (austereDnf ty m T₁) (austereDnf ty n T₂)))
          (austereDnf ty p T₃))
      = austereDnf ty ((m.seq n).seq p) ((T₁ ++ T₂) ++ T₃) := by
  have hTC₁₂ : ∀ a ∈ T₁ ++ T₂,
      a.TypeConsistent (tableOn ty (m.seq n).apex) := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact TypeConsistent_tableOn_mono ty Finset.subset_union_left
        (hw₁ a h) (hTC₁ a h)
    · exact TypeConsistent_tableOn_mono ty Finset.subset_union_right
        (hw₂ a h) (hTC₂ a h)
  have hw₁₂ : ∀ a ∈ T₁ ++ T₂,
      ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ (m.seq n).apex := by
    intro a ha w hww
    rcases List.mem_append.mp ha with h | h
    · exact Finset.mem_union_left _ (hw₁ a h w hww)
    · exact Finset.mem_union_right _ (hw₂ a h w hww)
  rw [theta_comp ty m n T₁ T₂ hTC₁ hw₁ hTC₂ hw₂,
    theta_comp ty (m.seq n) p (T₁ ++ T₂) T₃ hTC₁₂ hw₁₂ hTC₃ hw₃]

/-- Right-nested route, dually. -/
theorem theta_comp3_right (m : AlignedLoose X Y) (n : AlignedLoose Y Z)
    (p : AlignedLoose Z V) (T₁ T₂ T₃ : List PrimApp)
    (hTC₁ : ∀ a ∈ T₁, a.TypeConsistent (tableOn ty m.apex))
    (hw₁ : ∀ a ∈ T₁, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ m.apex)
    (hTC₂ : ∀ a ∈ T₂, a.TypeConsistent (tableOn ty n.apex))
    (hw₂ : ∀ a ∈ T₂, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ n.apex)
    (hTC₃ : ∀ a ∈ T₃, a.TypeConsistent (tableOn ty p.apex))
    (hw₃ : ∀ a ∈ T₃, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ p.apex) :
    dnfPull (splitTot ty m (n.seq p))
        (dnfBoxplus (austereDnf ty m T₁)
          (dnfPull (splitTot ty n p)
            (dnfBoxplus (austereDnf ty n T₂) (austereDnf ty p T₃))))
      = austereDnf ty (m.seq (n.seq p)) (T₁ ++ (T₂ ++ T₃)) := by
  have hTC₂₃ : ∀ a ∈ T₂ ++ T₃,
      a.TypeConsistent (tableOn ty (n.seq p).apex) := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact TypeConsistent_tableOn_mono ty Finset.subset_union_left
        (hw₂ a h) (hTC₂ a h)
    · exact TypeConsistent_tableOn_mono ty Finset.subset_union_right
        (hw₃ a h) (hTC₃ a h)
  have hw₂₃ : ∀ a ∈ T₂ ++ T₃,
      ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ (n.seq p).apex := by
    intro a ha w hww
    rcases List.mem_append.mp ha with h | h
    · exact Finset.mem_union_left _ (hw₂ a h w hww)
    · exact Finset.mem_union_right _ (hw₃ a h w hww)
  rw [theta_comp ty n p T₂ T₃ hTC₂ hw₂ hTC₃ hw₃,
    theta_comp ty m (n.seq p) T₁ (T₂ ++ T₃) hTC₁ hw₁ hTC₂₃ hw₂₃]

/-- The two flat forms coincide along strict associativity: composing
`theta_comp3_left`, this bridge, and `theta_comp3_right` says the two
compositor routes agree — associativity of the composite on the austere
face, with no comparison cell left over. -/
theorem austereDnf_assoc_heq (m : AlignedLoose X Y) (n : AlignedLoose Y Z)
    (p : AlignedLoose Z V) (T₁ T₂ T₃ : List PrimApp) :
    austereDnf ty ((m.seq n).seq p) ((T₁ ++ T₂) ++ T₃)
      ≍ austereDnf ty (m.seq (n.seq p)) (T₁ ++ (T₂ ++ T₃)) :=
  austereDnf_congr_heq ty (AlignedLoose.seq_assoc m n p)
    (List.append_assoc T₁ T₂ T₃)

/-! ## Substitutability

Composition respects semantic equivalence: components with equal
θ-images are interchangeable in any composite.  The congruence property
of the possibilistic semantics. -/

/-- Region-level congruence of binary composition. -/
theorem admRegion_append_congr (m : AlignedLoose X Y) (n : AlignedLoose Y Z)
    {T₁ T₁' T₂ T₂' : List PrimApp}
    (h₁ : AdmRegion ty m T₁ = AdmRegion ty m T₁')
    (h₂ : AdmRegion ty n T₂ = AdmRegion ty n T₂')
    (hTC₁ : ∀ a ∈ T₁, a.TypeConsistent (tableOn ty m.apex))
    (hw₁ : ∀ a ∈ T₁, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ m.apex)
    (hTC₂ : ∀ a ∈ T₂, a.TypeConsistent (tableOn ty n.apex))
    (hw₂ : ∀ a ∈ T₂, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ n.apex)
    (hTC₁' : ∀ a ∈ T₁', a.TypeConsistent (tableOn ty m.apex))
    (hw₁' : ∀ a ∈ T₁', ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ m.apex)
    (hTC₂' : ∀ a ∈ T₂', a.TypeConsistent (tableOn ty n.apex))
    (hw₂' : ∀ a ∈ T₂', ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ n.apex) :
    AdmRegion ty (m.seq n) (T₁ ++ T₂)
      = AdmRegion ty (m.seq n) (T₁' ++ T₂') := by
  rw [admRegion_append ty m n T₁ T₂ hTC₁ hw₁ hTC₂ hw₂,
    admRegion_append ty m n T₁' T₂' hTC₁' hw₁' hTC₂' hw₂', h₁, h₂]

/-- **Substitutability**: components with equal θ-images are
interchangeable in any binary composite.  A certified claim about a
component's possibilistic interface is a claim about every
presentation of that interface, in every wiring context. -/
theorem austereDnf_subst (m : AlignedLoose X Y) (n : AlignedLoose Y Z)
    {T₁ T₁' T₂ T₂' : List PrimApp}
    (h₁ : austereDnf ty m T₁ = austereDnf ty m T₁')
    (h₂ : austereDnf ty n T₂ = austereDnf ty n T₂')
    (hTC₁ : ∀ a ∈ T₁, a.TypeConsistent (tableOn ty m.apex))
    (hw₁ : ∀ a ∈ T₁, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ m.apex)
    (hTC₂ : ∀ a ∈ T₂, a.TypeConsistent (tableOn ty n.apex))
    (hw₂ : ∀ a ∈ T₂, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ n.apex)
    (hTC₁' : ∀ a ∈ T₁', a.TypeConsistent (tableOn ty m.apex))
    (hw₁' : ∀ a ∈ T₁', ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ m.apex)
    (hTC₂' : ∀ a ∈ T₂', a.TypeConsistent (tableOn ty n.apex))
    (hw₂' : ∀ a ∈ T₂', ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ n.apex) :
    austereDnf ty (m.seq n) (T₁ ++ T₂)
      = austereDnf ty (m.seq n) (T₁' ++ T₂') :=
  (austereDnf_eq_iff ty _ _ _).mpr
    (admRegion_append_congr ty m n
      ((austereDnf_eq_iff ty m T₁ T₁').mp h₁)
      ((austereDnf_eq_iff ty n T₂ T₂').mp h₂)
      hTC₁ hw₁ hTC₂ hw₂ hTC₁' hw₁' hTC₂' hw₂')

/-! ## Infeasibility propagates outward; feasibility does not -/

/-- An infeasible left component makes the composite infeasible. -/
theorem admRegion_append_empty_left (m : AlignedLoose X Y)
    (n : AlignedLoose Y Z) {T₁ T₂ : List PrimApp}
    (h : AdmRegion ty m T₁ = ∅)
    (hTC₁ : ∀ a ∈ T₁, a.TypeConsistent (tableOn ty m.apex))
    (hw₁ : ∀ a ∈ T₁, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ m.apex)
    (hTC₂ : ∀ a ∈ T₂, a.TypeConsistent (tableOn ty n.apex))
    (hw₂ : ∀ a ∈ T₂, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ n.apex) :
    AdmRegion ty (m.seq n) (T₁ ++ T₂) = ∅ := by
  rw [admRegion_append ty m n T₁ T₂ hTC₁ hw₁ hTC₂ hw₂, h]
  simp

/-- An infeasible right component makes the composite infeasible. -/
theorem admRegion_append_empty_right (m : AlignedLoose X Y)
    (n : AlignedLoose Y Z) {T₁ T₂ : List PrimApp}
    (h : AdmRegion ty n T₂ = ∅)
    (hTC₁ : ∀ a ∈ T₁, a.TypeConsistent (tableOn ty m.apex))
    (hw₁ : ∀ a ∈ T₁, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ m.apex)
    (hTC₂ : ∀ a ∈ T₂, a.TypeConsistent (tableOn ty n.apex))
    (hw₂ : ∀ a ∈ T₂, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ n.apex) :
    AdmRegion ty (m.seq n) (T₁ ++ T₂) = ∅ := by
  rw [admRegion_append ty m n T₁ T₂ hTC₁ hw₁ hTC₂ hw₂, h]
  simp

/-- An infeasible diagram denotes the bottom credal body: the
zero-joint singleton, never the empty set of beliefs. -/
theorem suppIn_admRegion_empty (m : AlignedLoose X Y)
    {T : List PrimApp} (h : AdmRegion ty m T = ∅) :
    suppIn (AdmRegion ty m T)
      = {Joint.zero (Pat.Tot (alignedPat ty m))} := by
  rw [h]
  exact suppIn_empty

/-! ## The share-mode witness: feasible parts, infeasible composite

The minimal instance of variable sharing gone infeasible: two constant
sources demanding different values of one shared wire.  Each component
is feasible in isolation; the composite admits no valuation.  This is
the converse boundary of the propagation theorems above — infeasibility
of a composite does *not* locate in a component. -/

/-- The constant witness state: every wire of the roster carries the
designated typed value. -/
def constState {τ : TensorType} (c : TensorValue τ) (W : Finset Wire) :
    states (ctxIface W) := fun _ => some ⟨τ, c⟩

theorem constState_conformant {w : Wire} {τ : TensorType}
    (hty : ty w = some τ) (c : TensorValue τ) :
    Conformant ty {w} (constState c {w}) := by
  intro w'
  have hw : w'.1 = w := Finset.mem_singleton.mp w'.2
  show (Option.some (⟨τ, c⟩ : Σ τ' : TensorType, TensorValue τ')).map
      Sigma.fst = ty w'.1
  rw [hw, hty]
  rfl

/-- Reading a valuation's entry at a wire whose table type is known. -/
theorem entryFlat_eq_of_wireType {H : Hypernet} (σ : H.Valuation)
    {w : Wire} {τ : TensorType} (h : H.wireType w = some τ) (i : ℕ) :
    σ.entryFlat w i = (σ w τ h).entryE i := by
  unfold Hypernet.Valuation.entryFlat
  split
  · next h' => rw [h'] at h; exact absurd h (by simp)
  · next τ' h' =>
      obtain rfl : τ' = τ := by
        rw [h'] at h; exact Option.some.inj h
      rfl

/-- A constant source on one wire is feasible: the constant state
witnesses it. -/
theorem share_feasible {w : Wire} {τ : TensorType} (hty : ty w = some τ)
    (c : TensorValue τ) :
    (AdmRegion ty (AlignedLoose.unit {w})
      [PrimApp.const τ c w]).Nonempty := by
  refine ⟨⟨constState c {w}, constState c {w},
    constState c {w}, constState_conformant ty hty c,
    fun _ => rfl, fun _ => rfl⟩, ?_⟩
  intro a ha
  rw [List.mem_singleton] at ha
  subst ha
  intro i
  have hwt : (vacNet (tableOn ty ({w} : Finset Wire))).wireType w
      = some τ := by
    show tableOn ty {w} w = some τ
    rw [tableOn_pos ty (Finset.mem_singleton_self w), hty]
  have hstep := entryFlat_eq_of_wireType
    (toValuation ty (constState_conformant ty hty c)) hwt i
  exact hstep.trans rfl

/-- **Feasibility is not compositional**: two feasible constant sources
sharing one wire compose to an infeasible whole, whenever their
constants differ at any entry.  The seam is where composites go
infeasible. -/
theorem share_contradiction {w : Wire} {τ : TensorType}
    (c₁ c₂ : TensorValue τ) {i₀ : ℕ}
    (hne : c₁.entryE i₀ ≠ c₂.entryE i₀) :
    AdmRegion ty
        ((AlignedLoose.unit {w}).seq (AlignedLoose.unit {w}))
        ([PrimApp.const τ c₁ w] ++ [PrimApp.const τ c₂ w]) = ∅ := by
  ext t
  simp only [mem_admRegion_iff, Set.mem_empty_iff_false, iff_false]
  intro hcon
  have h₁ := hcon (PrimApp.const τ c₁ w)
    (List.mem_append_left _ (List.mem_singleton_self _))
  have h₂ := hcon (PrimApp.const τ c₂ w)
    (List.mem_append_right _ (List.mem_singleton_self _))
  exact hne ((h₁ i₀).symm.trans (h₂ i₀))

/-! ## Naturality against the compositor

Renaming a composite is the composite of the renamings.  On θ-images
this is the hexagon closing `theta_comp` against `theta_rename`; at the
state level the square commutes definitionally — the split comparison
of the content-addressed stratum has no moving parts. -/

/-- Cells with one shared global map compose along `seq`. -/
def AlignedCell.seqCell {m : AlignedLoose X Y} {n : AlignedLoose Y Z}
    {m' : AlignedLoose X' Y'} {n' : AlignedLoose Y' Z'}
    (c₁ : AlignedCell ty m m') (c₂ : AlignedCell ty n n')
    (hmap : c₁.map = c₂.map) :
    AlignedCell ty (m.seq n) (m'.seq n') where
  map := c₁.map
  mem w hw := by
    rcases Finset.mem_union.mp hw with h | h
    · exact Finset.mem_union_left _ (c₁.mem w h)
    · rw [hmap]; exact Finset.mem_union_right _ (c₂.mem w h)
  ty_eq w hw := by
    rcases Finset.mem_union.mp hw with h | h
    · exact c₁.ty_eq w h
    · rw [hmap]; exact c₂.ty_eq w h
  left_mem := c₁.left_mem
  right_mem w hw := by rw [hmap]; exact c₂.right_mem w hw

/-- Restrict a cell between composites to its left components. -/
def AlignedCell.restrictLeft {m : AlignedLoose X Y} {n : AlignedLoose Y Z}
    {m' : AlignedLoose X' Y'} {n' : AlignedLoose Y' Z'}
    (c : AlignedCell ty (m.seq n) (m'.seq n'))
    (hm : ∀ w ∈ m.apex, c.map w ∈ m'.apex)
    (hY : ∀ w ∈ Y, c.map w ∈ Y') :
    AlignedCell ty m m' where
  map := c.map
  mem := hm
  ty_eq w hw := c.ty_eq w (Finset.mem_union_left _ hw)
  left_mem := c.left_mem
  right_mem := hY

/-- Restrict a cell between composites to its right components. -/
def AlignedCell.restrictRight {m : AlignedLoose X Y} {n : AlignedLoose Y Z}
    {m' : AlignedLoose X' Y'} {n' : AlignedLoose Y' Z'}
    (c : AlignedCell ty (m.seq n) (m'.seq n'))
    (hn : ∀ w ∈ n.apex, c.map w ∈ n'.apex)
    (hY : ∀ w ∈ Y, c.map w ∈ Y') :
    AlignedCell ty n n' where
  map := c.map
  mem := hn
  ty_eq w hw := c.ty_eq w (Finset.mem_union_right _ hw)
  left_mem := hY
  right_mem := c.right_mem

/-- **The state-level naturality square, left projection —
definitionally**: splitting after renaming is renaming after splitting.
On the content-addressed stratum the square has no comparison data. -/
theorem compFst_splitTot_renameTot {m : AlignedLoose X Y}
    {n : AlignedLoose Y Z} {m' : AlignedLoose X' Y'}
    {n' : AlignedLoose Y' Z'}
    (c : AlignedCell ty (m.seq n) (m'.seq n'))
    (hm : ∀ w ∈ m.apex, c.map w ∈ m'.apex)
    (hY : ∀ w ∈ Y, c.map w ∈ Y')
    (t : Pat.Tot (alignedPat ty (m'.seq n'))) :
    Pat.compFst _ _ (splitTot ty m n (renameTot ty c t))
      = renameTot ty (c.restrictLeft ty hm hY)
          (Pat.compFst _ _ (splitTot ty m' n' t)) :=
  rfl

/-- The state-level naturality square, right projection —
definitionally. -/
theorem compSnd_splitTot_renameTot {m : AlignedLoose X Y}
    {n : AlignedLoose Y Z} {m' : AlignedLoose X' Y'}
    {n' : AlignedLoose Y' Z'}
    (c : AlignedCell ty (m.seq n) (m'.seq n'))
    (hn : ∀ w ∈ n.apex, c.map w ∈ n'.apex)
    (hY : ∀ w ∈ Y, c.map w ∈ Y')
    (t : Pat.Tot (alignedPat ty (m'.seq n'))) :
    Pat.compSnd _ _ (splitTot ty m n (renameTot ty c t))
      = renameTot ty (c.restrictRight ty hn hY)
          (Pat.compSnd _ _ (splitTot ty m' n' t)) :=
  rfl

/-- **The naturality hexagon**: renaming a composite equals composing
the renamings, on θ-images.  The consistency hypotheses for the renamed
lists transfer along the cell (they are stated as hypotheses here; the
transfer is `TypeConsistent_congr` along the cell's typing law). -/
theorem theta_rename_seq {m : AlignedLoose X Y} {n : AlignedLoose Y Z}
    {m' : AlignedLoose X' Y'} {n' : AlignedLoose Y' Z'}
    (c₁ : AlignedCell ty m m') (c₂ : AlignedCell ty n n')
    (hmap : c₁.map = c₂.map) (T₁ T₂ : List PrimApp)
    (hTC₁ : ∀ a ∈ T₁, a.TypeConsistent (tableOn ty m.apex))
    (hw₁ : ∀ a ∈ T₁, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ m.apex)
    (hTC₂ : ∀ a ∈ T₂, a.TypeConsistent (tableOn ty n.apex))
    (hw₂ : ∀ a ∈ T₂, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ n.apex)
    (hTC₁' : ∀ a ∈ T₁.map (PrimApp.rename c₁.map),
      a.TypeConsistent (tableOn ty m'.apex))
    (hw₁' : ∀ a ∈ T₁.map (PrimApp.rename c₁.map),
      ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ m'.apex)
    (hTC₂' : ∀ a ∈ T₂.map (PrimApp.rename c₂.map),
      a.TypeConsistent (tableOn ty n'.apex))
    (hw₂' : ∀ a ∈ T₂.map (PrimApp.rename c₂.map),
      ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ n'.apex) :
    dnfPull (renameTot ty (AlignedCell.seqCell ty c₁ c₂ hmap))
        (austereDnf ty (m.seq n) (T₁ ++ T₂))
      = dnfPull (splitTot ty m' n')
          (dnfBoxplus
            (dnfPull (renameTot ty c₁) (austereDnf ty m T₁))
            (dnfPull (renameTot ty c₂) (austereDnf ty n T₂))) := by
  have hTC₁₂ : ∀ a ∈ T₁ ++ T₂,
      a.TypeConsistent (tableOn ty (m.seq n).apex) := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact TypeConsistent_tableOn_mono ty Finset.subset_union_left
        (hw₁ a h) (hTC₁ a h)
    · exact TypeConsistent_tableOn_mono ty Finset.subset_union_right
        (hw₂ a h) (hTC₂ a h)
  have hw₁₂ : ∀ a ∈ T₁ ++ T₂,
      ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ (m.seq n).apex := by
    intro a ha w hww
    rcases List.mem_append.mp ha with h | h
    · exact Finset.mem_union_left _ (hw₁ a h w hww)
    · exact Finset.mem_union_right _ (hw₂ a h w hww)
  rw [theta_rename ty (AlignedCell.seqCell ty c₁ c₂ hmap) (T₁ ++ T₂)
      hTC₁₂ hw₁₂,
    theta_rename ty c₁ T₁ hTC₁ hw₁, theta_rename ty c₂ T₂ hTC₂ hw₂,
    theta_comp ty m' n' _ _ hTC₁' hw₁' hTC₂' hw₂']
  show austereDnf ty (m'.seq n')
      ((T₁ ++ T₂).map (PrimApp.rename c₁.map)) = _
  rw [List.map_append]
  congr 1
  rw [hmap]

end

end SuFunctor

/-!  ## Axiom receipts (in-package convention: `#print axioms`) -/

#print axioms PPLC.PrimApp.TypeConsistent_congr
#print axioms SuFunctor.TypeConsistent_tableOn_mono
#print axioms SuFunctor.AlignedLoose.seq_assoc
#print axioms SuFunctor.AlignedLoose.unit_seq
#print axioms SuFunctor.AlignedLoose.seq_unit
#print axioms SuFunctor.theta_comp3_left
#print axioms SuFunctor.theta_comp3_right
#print axioms SuFunctor.austereDnf_assoc_heq
#print axioms SuFunctor.admRegion_append_congr
#print axioms SuFunctor.austereDnf_subst
#print axioms SuFunctor.admRegion_append_empty_left
#print axioms SuFunctor.admRegion_append_empty_right
#print axioms SuFunctor.suppIn_admRegion_empty
#print axioms SuFunctor.share_feasible
#print axioms SuFunctor.share_contradiction
#print axioms SuFunctor.compFst_splitTot_renameTot
#print axioms SuFunctor.compSnd_splitTot_renameTot
#print axioms SuFunctor.theta_rename_seq
