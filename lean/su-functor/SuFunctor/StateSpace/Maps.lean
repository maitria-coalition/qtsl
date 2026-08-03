import SuFunctor.StateSpace.Pieces

/-! # Countably-piecewise-polynomial maps (rational coefficients)

The morphisms of the ω-semialgebraic class: the polynomial stratum of the
PAP maps of Lee et al. / Huot–Lew–Mansinghka–Staton (arXiv:2302.10636,
PAP definition).  A map is **countably-piecewise-polynomial on `V`**
(`IsPiecewisePolyOn`) if some countable family of basic pieces covers `V`
and the map agrees with a (globally defined, rational-coefficient)
polynomial map on each piece.

The coefficient pin on piece-*functions* is forced, not chosen: carving
data is pinned to ℚ (exactness — see `Pieces.lean`), and composition
substitutes piece-functions into carving polynomials, so any wider
function class would carve its refined pieces outside the class.  The
general law (verified adversarially for the analytic strata): a piecewise
class composes iff its carving class absorbs precomposition by its
function class — carving may exceed functions, never lag.  At exact
(ℚ-pinned) carving this forces ℚ-polynomial piece-functions; poly/poly
over ℚ is the unique exactness-preserving composition-closed dial.

Three departures from the paper's phrasing, mechanization-motivated and
extensionally harmless:

* **Cover, not partition**: pieces may overlap (where they do, their
  polynomials agree on `V`, both being the map).  Composition then needs
  only substitution and pair-reindexing — no disjointification.
* **Global piece-polynomials**: the paper's per-piece functions extend
  analytically to open neighborhoods; polynomials extend globally for
  free, so the extension clause degenerates.
* **Raw codomain**: the property mentions no codomain carving, so
  restriction/corestriction along subset inclusions preserves the
  witness family on the nose.

The composition theorem (`IsPiecewisePolyOn.comp`) is the load-bearing
result — it is what makes the class a category — and its proof consumes
substitution only (`basicSet_subst`): the mechanization is itself the
witness that no quantifier elimination is needed for preimages.  The
`graphSet` and `eqLocus` theorems record that graphs and agreement loci
are ω-semialgebraic — the properties that fail for "pointwise polynomial
selection without pieces" (any countable-range map is such a selection,
with arbitrary graph and level sets).
-/

namespace SuFunctor.StateSpace

open MvPolynomial Set

noncomputable section

/-- A rational-coefficient polynomial map `ℝⁿ → ℝᵐ`: one polynomial per
output coordinate. -/
def PolyMap (n m : ℕ) : Type :=
  Fin m → MvPolynomial (Fin n) ℚ

namespace PolyMap

variable {n m k : ℕ}

/-- Evaluate a polynomial map at a real point. -/
def apply (P : PolyMap n m) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun j => aeval x (P j)

/-- The identity polynomial map. -/
protected def id (n : ℕ) : PolyMap n n := fun i => X i

@[simp] lemma apply_id (x : Fin n → ℝ) : (PolyMap.id n).apply x = x :=
  funext fun i => aeval_X x i

/-- Composition by substitution. -/
def comp (Q : PolyMap m k) (P : PolyMap n m) : PolyMap n k :=
  fun j => bind₁ P (Q j)

@[simp] lemma apply_comp (Q : PolyMap m k) (P : PolyMap n m) (x : Fin n → ℝ) :
    (Q.comp P).apply x = Q.apply (P.apply x) :=
  funext fun j => aeval_bind₁ x P (Q j)

/-- The constant polynomial map at a rational point. -/
def const (n : ℕ) (c : Fin m → ℚ) : PolyMap n m := fun j => C (c j)

@[simp] lemma apply_const (c : Fin m → ℚ) (x : Fin n → ℝ) :
    (const n c).apply x = fun j => algebraMap ℚ ℝ (c j) :=
  funext fun j => by simp [const, apply]

end PolyMap

variable {n m k : ℕ}

/-- `f`, defined on the subtype of `V`, is **countably-piecewise-polynomial
on `V`**: a countable family of basic pieces covers `V`, and on (the trace
in `V` of) each piece, `f` is the restriction of a rational polynomial map.

The codomain is the raw ambient type: the property of a morphism into a
subset `W` is the property of its coercion, so restriction/corestriction
along subset inclusions preserves the witness family on the nose. -/
def IsPiecewisePolyOn (V : Set (Fin n → ℝ)) (f : V → Fin m → ℝ) : Prop :=
  ∃ F : ℕ → List (PolyCond n) × PolyMap n m,
    (V ⊆ ⋃ i, BasicSet (F i).1) ∧
    ∀ (i : ℕ) (x : V), (x : Fin n → ℝ) ∈ BasicSet (F i).1 → f x = (F i).2.apply x

namespace IsPiecewisePolyOn

variable {V : Set (Fin n → ℝ)} {W : Set (Fin m → ℝ)}

/-- The coercion (identity/inclusion) map is piecewise-polynomial: one
piece, the identity polynomial map. -/
protected lemma id (V : Set (Fin n → ℝ)) :
    IsPiecewisePolyOn V (fun x : V => (x : Fin n → ℝ)) := by
  refine ⟨fun _ => ([], PolyMap.id n), ?_, ?_⟩
  · intro x _; exact mem_iUnion.mpr ⟨0, by simp⟩
  · intro i x _; simp

/-- Constant maps at rational points are piecewise-polynomial. -/
protected lemma const (V : Set (Fin n → ℝ)) (c : Fin m → ℚ) :
    IsPiecewisePolyOn V (fun _ : V => fun j => algebraMap ℚ ℝ (c j)) := by
  refine ⟨fun _ => ([], PolyMap.const n c), ?_, ?_⟩
  · intro x _; exact mem_iUnion.mpr ⟨0, by simp⟩
  · intro i x _; simp

/-- Restrictions of global polynomial maps are piecewise-polynomial. -/
protected lemma polyMap (V : Set (Fin n → ℝ)) (P : PolyMap n m) :
    IsPiecewisePolyOn V (fun x : V => P.apply x) := by
  refine ⟨fun _ => ([], P), ?_, ?_⟩
  · intro x _; exact mem_iUnion.mpr ⟨0, by simp⟩
  · intro i x _; rfl

/-- Transport along a pointwise equality. -/
protected lemma congr {f g : V → Fin m → ℝ} (h : ∀ x, f x = g x)
    (hf : IsPiecewisePolyOn V f) : IsPiecewisePolyOn V g := by
  obtain ⟨F, hcov, hagree⟩ := hf
  exact ⟨F, hcov, fun i x hx => (h x).symm.trans (hagree i x hx)⟩

/-- **Composition closure** — the load-bearing theorem of the class.
If `f : V → W` is piecewise-polynomial (as a map into the ambient of `W`)
and `g` is piecewise-polynomial on `W`, then `g ∘ f` is piecewise-
polynomial on `V`, with pieces `Aᵢ ∩ Pᵢ⁻¹(Bⱼ)` (an intersection of basic
sets, by substitution) and polynomials `Qⱼ ∘ Pᵢ` (by `bind₁`).  Nothing
beyond substitution is consumed: no projection, no quantifier
elimination, no piece disjointification. -/
protected lemma comp {g : W → Fin k → ℝ} {f : V → W}
    (hg : IsPiecewisePolyOn W g)
    (hf : IsPiecewisePolyOn V (fun x => (f x : Fin m → ℝ))) :
    IsPiecewisePolyOn V (fun x => g (f x)) := by
  obtain ⟨F, hFcov, hFagree⟩ := hf
  obtain ⟨G, hGcov, hGagree⟩ := hg
  refine ⟨fun p =>
    ((F (Nat.pairEquiv.symm p).1).1 ++
      ((G (Nat.pairEquiv.symm p).2).1.map
        (PolyCond.subst · (F (Nat.pairEquiv.symm p).1).2)),
      (G (Nat.pairEquiv.symm p).2).2.comp (F (Nat.pairEquiv.symm p).1).2),
    ?_, ?_⟩
  · -- cover
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hFcov hy)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hGcov (f ⟨y, hy⟩).2)
    refine mem_iUnion.mpr ⟨Nat.pairEquiv (i, j), ?_⟩
    simp only [Equiv.symm_apply_apply, basicSet_append, mem_inter_iff]
    refine ⟨hi, ?_⟩
    rw [basicSet_subst]
    show (F i).2.apply y ∈ BasicSet (G j).1
    have hagree : (f ⟨y, hy⟩ : Fin m → ℝ) = (F i).2.apply y :=
      hFagree i ⟨y, hy⟩ hi
    exact hagree ▸ hj
  · -- agreement
    intro p x hx
    set i := (Nat.pairEquiv.symm p).1 with hi_def
    set j := (Nat.pairEquiv.symm p).2 with hj_def
    rw [basicSet_append, mem_inter_iff] at hx
    obtain ⟨hxF, hxG⟩ := hx
    have hfx : (f x : Fin m → ℝ) = (F i).2.apply x := hFagree i x hxF
    have hmem : ((f x : Fin m → ℝ)) ∈ BasicSet (G j).1 := by
      have h' := (basicSet_subst (G j).1 (F i).2 x).mp hxG
      rw [hfx]
      exact h'
    calc g (f x) = (G j).2.apply (f x) := hGagree j (f x) hmem
    _ = (G j).2.apply ((F i).2.apply x) := by rw [hfx]
    _ = ((G j).2.comp (F i).2).apply x := (PolyMap.apply_comp _ _ _).symm

end IsPiecewisePolyOn

/-- The graph of a map from `V ⊆ ℝⁿ` to `ℝᵐ`, as a subset of `ℝ^(n+m)`
(first `n` coordinates the input, last `m` the output). -/
def graphSet (V : Set (Fin n → ℝ)) (f : V → Fin m → ℝ) :
    Set (Fin (n + m) → ℝ) :=
  {z | ∃ h : (fun i => z (Fin.castAdd m i)) ∈ V,
    (fun j => z (Fin.natAdd n j)) = f ⟨_, h⟩}

section AgreementCarving

/-- Rename a condition on `ℝⁿ` to a condition on the first `n` coordinates
of `ℝ^(n+m)`. -/
def PolyCond.renameL (c : PolyCond n) (m : ℕ) : PolyCond (n + m) :=
  ⟨rename (Fin.castAdd m) c.poly, c.sign⟩

lemma PolyCond.holds_renameL (c : PolyCond n) {m : ℕ} (z : Fin (n + m) → ℝ) :
    (c.renameL m).holds z ↔ c.holds (fun i => z (Fin.castAdd m i)) := by
  obtain ⟨p, s⟩ := c
  cases s <;>
    simp [PolyCond.renameL, PolyCond.holds, aeval_rename, Function.comp_def]

/-- Rename a condition on `ℝᵐ` to a condition on the last `m` coordinates
of `ℝ^(n+m)`. -/
def PolyCond.renameR (c : PolyCond m) (n : ℕ) : PolyCond (n + m) :=
  ⟨rename (Fin.natAdd n) c.poly, c.sign⟩

lemma PolyCond.holds_renameR (c : PolyCond m) {n : ℕ} (z : Fin (n + m) → ℝ) :
    (c.renameR n).holds z ↔ c.holds (fun j => z (Fin.natAdd n j)) := by
  obtain ⟨p, s⟩ := c
  cases s <;>
    simp [PolyCond.renameR, PolyCond.holds, aeval_rename, Function.comp_def]

lemma basicSet_map_renameL (L : List (PolyCond n)) {m : ℕ} (z : Fin (n + m) → ℝ) :
    z ∈ BasicSet (L.map (PolyCond.renameL · m)) ↔
      (fun i => z (Fin.castAdd m i)) ∈ BasicSet L := by
  simp only [mem_basicSet, List.mem_map]
  constructor
  · rintro h c hc
    exact (c.holds_renameL z).mp (h _ ⟨c, hc, rfl⟩)
  · rintro h - ⟨c, hc, rfl⟩
    exact (c.holds_renameL z).mpr (h c hc)

lemma basicSet_map_renameR (L : List (PolyCond m)) {n : ℕ} (z : Fin (n + m) → ℝ) :
    z ∈ BasicSet (L.map (PolyCond.renameR · n)) ↔
      (fun j => z (Fin.natAdd n j)) ∈ BasicSet L := by
  simp only [mem_basicSet, List.mem_map]
  constructor
  · rintro h c hc
    exact (c.holds_renameR z).mp (h _ ⟨c, hc, rfl⟩)
  · rintro h - ⟨c, hc, rfl⟩
    exact (c.holds_renameR z).mpr (h c hc)

/-- The pair of conditions expressing `q = 0`. -/
def eqConds (q : MvPolynomial (Fin k) ℚ) : List (PolyCond k) :=
  [⟨q, .le⟩, ⟨-q, .le⟩]

lemma mem_basicSet_eqConds (q : MvPolynomial (Fin k) ℚ) (z : Fin k → ℝ) :
    z ∈ BasicSet (eqConds q) ↔ aeval z q = 0 := by
  constructor
  · intro h
    have h₁ := h ⟨q, .le⟩ (by simp [eqConds])
    have h₂ := h ⟨-q, .le⟩ (by simp [eqConds])
    simp only [PolyCond.holds_le, map_neg, neg_nonpos] at h₁ h₂
    exact le_antisymm h₁ h₂
  · intro h c hc
    have hcc : c = ⟨q, .le⟩ ∨ c = ⟨-q, .le⟩ := by simpa [eqConds] using hc
    rcases hcc with rfl | rfl <;> simp [PolyCond.holds, h]

/-- The list of conditions expressing that a polynomial map's outputs equal
the last `m` coordinates: `z_right = P(z_left)`. -/
def graphConds (P : PolyMap n m) : List (PolyCond (n + m)) :=
  (List.finRange m).flatMap fun j =>
    eqConds (X (Fin.natAdd n j) - rename (Fin.castAdd m) (P j))

lemma mem_basicSet_graphConds (P : PolyMap n m) (z : Fin (n + m) → ℝ) :
    z ∈ BasicSet (graphConds P) ↔
      (fun j => z (Fin.natAdd n j)) = P.apply (fun i => z (Fin.castAdd m i)) := by
  simp only [graphConds, BasicSet, List.mem_flatMap, mem_setOf_eq]
  constructor
  · intro h
    funext j
    have hj : z ∈ BasicSet
        (eqConds (X (Fin.natAdd n j) - rename (Fin.castAdd m) (P j))) := by
      intro c hc
      exact h c ⟨j, List.mem_finRange j, hc⟩
    have hz := (mem_basicSet_eqConds _ z).mp hj
    simp only [map_sub, aeval_X, aeval_rename, sub_eq_zero] at hz
    simpa [PolyMap.apply, Function.comp_def] using hz
  · intro h c hc
    obtain ⟨j, -, hc⟩ := hc
    have hj : z ∈ BasicSet
        (eqConds (X (Fin.natAdd n j) - rename (Fin.castAdd m) (P j))) := by
      rw [mem_basicSet_eqConds]
      simp only [map_sub, aeval_X, aeval_rename]
      have := congrFun h j
      simpa [PolyMap.apply, Function.comp_def, sub_eq_zero] using this
    exact hj c hc

end AgreementCarving

/-- **The graph theorem**: the graph of a countably-piecewise-polynomial
map on an ω-semialgebraic domain is ω-semialgebraic.  (This is a theorem
that fails for pointwise polynomial selection without pieces: any map
with countable range is such a selection, with arbitrary graph.) -/
theorem IsOmegaSA.graphSet {V : Set (Fin n → ℝ)} {f : V → Fin m → ℝ}
    (hV : IsOmegaSA V) (hf : IsPiecewisePolyOn V f) :
    IsOmegaSA (graphSet V f) := by
  obtain ⟨C, hC⟩ := hV
  obtain ⟨F, hFcov, hFagree⟩ := hf
  refine ⟨fun p =>
    ((C (Nat.pairEquiv.symm p).1).map (PolyCond.renameL · m)) ++
      (((F (Nat.pairEquiv.symm p).2).1).map (PolyCond.renameL · m)) ++
      graphConds (F (Nat.pairEquiv.symm p).2).2, ?_⟩
  ext z
  constructor
  · rintro ⟨hzV, hzf⟩
    have hzC : (fun i => z (Fin.castAdd m i)) ∈ ⋃ c, BasicSet (C c) := hC ▸ hzV
    obtain ⟨c, hc⟩ := mem_iUnion.mp hzC
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hFcov hzV)
    refine mem_iUnion.mpr ⟨Nat.pairEquiv (c, i), ?_⟩
    simp only [Equiv.symm_apply_apply, basicSet_append, mem_inter_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [basicSet_map_renameL]; exact hc
    · rw [basicSet_map_renameL]; exact hi
    · rw [mem_basicSet_graphConds]
      exact hzf.trans (hFagree i ⟨_, hzV⟩ hi)
  · intro hz
    obtain ⟨p, hp⟩ := mem_iUnion.mp hz
    rw [basicSet_append, basicSet_append] at hp
    obtain ⟨⟨hpC, hpF⟩, hpG⟩ := hp
    have hzV : (fun i => z (Fin.castAdd m i)) ∈ V := by
      rw [hC]
      exact mem_iUnion.mpr ⟨(Nat.pairEquiv.symm p).1,
        (basicSet_map_renameL _ z).mp hpC⟩
    refine ⟨hzV, ?_⟩
    have hzF : (fun i => z (Fin.castAdd m i)) ∈
        BasicSet (F (Nat.pairEquiv.symm p).2).1 :=
      (basicSet_map_renameL _ z).mp hpF
    have hagree : f ⟨_, hzV⟩ = (F (Nat.pairEquiv.symm p).2).2.apply
        (fun i => z (Fin.castAdd m i)) :=
      hFagree (Nat.pairEquiv.symm p).2 ⟨_, hzV⟩ hzF
    exact ((mem_basicSet_graphConds _ z).mp hpG).trans hagree.symm

/-- The agreement locus of two maps on `V`, as an ambient subset. -/
def eqLocus (V : Set (Fin n → ℝ)) (f g : V → Fin m → ℝ) :
    Set (Fin n → ℝ) :=
  {y | ∃ h : y ∈ V, f ⟨y, h⟩ = g ⟨y, h⟩}

/-- The list of conditions expressing `P = Q` as polynomial maps. -/
def eqMapConds (P Q : PolyMap n m) : List (PolyCond n) :=
  (List.finRange m).flatMap fun j => eqConds (P j - Q j)

lemma mem_basicSet_eqMapConds (P Q : PolyMap n m) (x : Fin n → ℝ) :
    x ∈ BasicSet (eqMapConds P Q) ↔ P.apply x = Q.apply x := by
  simp only [eqMapConds, BasicSet, List.mem_flatMap, mem_setOf_eq]
  constructor
  · intro h
    funext j
    have hj : x ∈ BasicSet (eqConds (P j - Q j)) := by
      intro c hc
      exact h c ⟨j, List.mem_finRange j, hc⟩
    have hx := (mem_basicSet_eqConds _ x).mp hj
    simpa [PolyMap.apply, map_sub, sub_eq_zero] using hx
  · intro h c hc
    obtain ⟨j, -, hc⟩ := hc
    have hj : x ∈ BasicSet (eqConds (P j - Q j)) := by
      rw [mem_basicSet_eqConds]
      have := congrFun h j
      simpa [PolyMap.apply, map_sub, sub_eq_zero] using this
    exact hj c hc

/-- **The equalizer theorem**: the agreement locus of two countably-
piecewise-polynomial maps on an ω-semialgebraic domain is ω-semialgebraic,
carved per piece-pair by the polynomial equations `Pᵢ = Qⱼ`.  (The second
theorem that fails for pointwise selection without pieces.) -/
theorem IsOmegaSA.eqLocus {V : Set (Fin n → ℝ)} {f g : V → Fin m → ℝ}
    (hV : IsOmegaSA V) (hf : IsPiecewisePolyOn V f) (hg : IsPiecewisePolyOn V g) :
    IsOmegaSA (eqLocus V f g) := by
  obtain ⟨C, hC⟩ := hV
  obtain ⟨F, hFcov, hFagree⟩ := hf
  obtain ⟨G, hGcov, hGagree⟩ := hg
  refine ⟨fun p =>
    C (Nat.pairEquiv.symm p).1 ++
      (F (Nat.pairEquiv.symm (Nat.pairEquiv.symm p).2).1).1 ++
      (G (Nat.pairEquiv.symm (Nat.pairEquiv.symm p).2).2).1 ++
      eqMapConds (F (Nat.pairEquiv.symm (Nat.pairEquiv.symm p).2).1).2
        (G (Nat.pairEquiv.symm (Nat.pairEquiv.symm p).2).2).2, ?_⟩
  ext y
  constructor
  · rintro ⟨hyV, hyfg⟩
    have hyC : y ∈ ⋃ c, BasicSet (C c) := hC ▸ hyV
    obtain ⟨c, hc⟩ := mem_iUnion.mp hyC
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hFcov hyV)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hGcov hyV)
    refine mem_iUnion.mpr ⟨Nat.pairEquiv (c, Nat.pairEquiv (i, j)), ?_⟩
    simp only [Equiv.symm_apply_apply, basicSet_append, mem_inter_iff]
    refine ⟨⟨⟨hc, hi⟩, hj⟩, ?_⟩
    rw [mem_basicSet_eqMapConds]
    calc (F i).2.apply y = f ⟨y, hyV⟩ := (hFagree i ⟨y, hyV⟩ hi).symm
    _ = g ⟨y, hyV⟩ := hyfg
    _ = (G j).2.apply y := hGagree j ⟨y, hyV⟩ hj
  · intro hy
    obtain ⟨p, hp⟩ := mem_iUnion.mp hy
    rw [basicSet_append, basicSet_append, basicSet_append] at hp
    obtain ⟨⟨⟨hpC, hpF⟩, hpG⟩, hpEq⟩ := hp
    have hyV : y ∈ V := hC ▸ mem_iUnion.mpr ⟨(Nat.pairEquiv.symm p).1, hpC⟩
    refine ⟨hyV, ?_⟩
    calc f ⟨y, hyV⟩ = _ := hFagree _ ⟨y, hyV⟩ hpF
    _ = _ := (mem_basicSet_eqMapConds _ _ y).mp hpEq
    _ = g ⟨y, hyV⟩ := (hGagree _ ⟨y, hyV⟩ hpG).symm

end

end SuFunctor.StateSpace
