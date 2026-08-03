import SuFunctor.StateSpace.Citizens
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Real.Cardinality

/-! # Adjudication receipts: the counterexamples that separate the definitions

Three refutation families, each a design decision's witness:

* **`natSet_not_finiteSA`** — `ℕ` is not a *finite* union of basic pieces:
  the countability axis is load-bearing (this is the theorem that the
  "drop countability" mutant must lose, and the reason the class exits
  every o-minimal structure).  Proof: a basic piece of `ℝ` containing
  arbitrarily large naturals contains a whole tail interval (finitely
  many roots + sign constancy beyond them), and tails contain
  non-naturals.
* **the `√` pair** (`graphSet_sqrtRaw_eq_basic` + `sqrt_not_piecewisePoly`)
  — the graph of `√·` on `[0,∞)` is a *single basic piece*, yet `√·` is
  not countably-piecewise-polynomial (a polynomial agreeing with `√` on
  an infinite set gives `q² = X`, impossible by degree parity).  So
  "morphism = graph is ω-semialgebraic" and "morphism = countably-
  piecewise-polynomial" are genuinely different classes; the category
  uses the latter, which composes by substitution.  (This is the
  finite-stratum face of the non-fullness of the inclusion into wider
  piecewise classes: `sin` plays the same role one stratum up, being
  ωPAP but not ω-semialgebraic.)
* **`omegaSA_not_balanced`** — cubing `ℝ → ℝ` is monic and epic but not
  an isomorphism (its inverse `∛` is not piecewise-polynomial, by the
  same degree parity: `q³ = X`); consequently the subobject lattice is
  strictly richer than the lattice of ω-semialgebraic subsets, and the
  category is not a topos.
-/

namespace SuFunctor.StateSpace

open MvPolynomial Set Polynomial CategoryTheory

noncomputable section

/-! ## The one-variable bridge -/

/-- `Fin 1`-variable rational polynomials as single-variable ones. -/
def toUni : MvPolynomial (Fin 1) ℚ →ₐ[ℚ] Polynomial ℚ :=
  MvPolynomial.aeval (fun _ => Polynomial.X)

/-- The real single-variable polynomial of a `Fin 1`-variable rational one. -/
def realUni (p : MvPolynomial (Fin 1) ℚ) : Polynomial ℝ :=
  (toUni p).map (algebraMap ℚ ℝ)

lemma eval_realUni (p : MvPolynomial (Fin 1) ℚ) (t : ℝ) :
    (realUni p).eval t = MvPolynomial.aeval (fun _ : Fin 1 => t) p := by
  rw [realUni, Polynomial.eval_map, ← Polynomial.aeval_def]
  induction p using MvPolynomial.induction_on with
  | C a => simp [toUni]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
      have htX : toUni (X i) = Polynomial.X := by
        simp [toUni]
      simp only [map_mul, htX, Polynomial.aeval_X, MvPolynomial.aeval_X, hp]

/-- Every point of the one-dimensional ambient is constant. -/
lemma eq_const (x : Fin 1 → ℝ) : x = fun _ => x 0 :=
  funext fun i => by rw [Subsingleton.elim i 0]

/-! ## Tails: sign constancy beyond the last root -/

/-- No sign change beyond the last root. -/
lemma eval_neg_beyond {q : Polynomial ℝ} {R₀ : ℝ}
    (hR₀ : ∀ x, q.IsRoot x → x ≤ R₀) {a b : ℝ}
    (ha : R₀ < a) (hb : R₀ < b) (hqa : q.eval a < 0) : q.eval b < 0 := by
  rcases lt_trichotomy (q.eval b) 0 with h | h | h
  · exact h
  · exact absurd (hR₀ b h) (not_le.mpr hb)
  · exfalso
    have h0 : (0 : ℝ) ∈ Set.uIcc (q.eval a) (q.eval b) :=
      Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt hqa, le_of_lt h⟩)
    obtain ⟨s, hs, hs0⟩ :=
      intermediate_value_uIcc (Continuous.continuousOn q.continuous) h0
    have hsR : s ≤ R₀ := hR₀ s hs0
    have hmin : min a b ≤ s := hs.1
    have : R₀ < min a b := lt_min ha hb
    linarith

/-- An infinite set of naturals reaches beyond any real bound. -/
lemma exists_nat_beyond {S : Set ℕ} (hS : S.Infinite) (R : ℝ) :
    ∃ k ∈ S, R < (k : ℝ) := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  have hsub : S ⊆ Set.Iic ⌈max R 0⌉₊ := fun k hk => by
    have h1 : (k : ℝ) ≤ (⌈max R 0⌉₊ : ℝ) :=
      le_trans (le_trans (h k hk) (le_max_left _ _)) (Nat.le_ceil _)
    exact Set.mem_Iic.mpr (Nat.cast_le.mp h1)
  exact hS ((Set.finite_Iic _).subset hsub)

/-- A condition satisfied by infinitely many naturals is satisfied on a
whole tail of the real line. -/
lemma eventually_holds_of_infinite_nat (c : PolyCond 1)
    (hc : {k : ℕ | c.holds (fun _ => (k : ℝ))}.Infinite) :
    ∃ R : ℝ, ∀ t : ℝ, R < t → c.holds (fun _ => t) := by
  obtain ⟨p, s⟩ := c
  have hEval : ∀ t : ℝ, MvPolynomial.aeval (fun _ : Fin 1 => t) p =
      (realUni p).eval t := fun t => (eval_realUni p t).symm
  by_cases hq0 : realUni p = 0
  · cases s
    · exact ⟨0, fun t _ => by
        rw [PolyCond.holds_le, hEval t, hq0]; simp⟩
    · exfalso
      obtain ⟨k, hk⟩ := hc.nonempty
      rw [Set.mem_setOf_eq, PolyCond.holds_lt, hEval, hq0] at hk
      simpa using hk
  · obtain ⟨R₀, hR₀⟩ := Polynomial.exists_max_root _ hq0
    obtain ⟨k, hkS, hkR⟩ := exists_nat_beyond hc R₀
    have hkne : (realUni p).eval (k : ℝ) ≠ 0 := fun h =>
      absurd (hR₀ _ h) (not_le.mpr hkR)
    cases s
    · -- `≤ 0`, strict at `k` since `k` is beyond the roots
      rw [Set.mem_setOf_eq, PolyCond.holds_le, hEval] at hkS
      have hklt : (realUni p).eval (k : ℝ) < 0 := lt_of_le_of_ne hkS hkne
      exact ⟨R₀, fun t ht => by
        rw [PolyCond.holds_le, hEval]
        exact le_of_lt (eval_neg_beyond hR₀ hkR ht hklt)⟩
    · rw [Set.mem_setOf_eq, PolyCond.holds_lt, hEval] at hkS
      exact ⟨R₀, fun t ht => by
        rw [PolyCond.holds_lt, hEval]
        exact eval_neg_beyond hR₀ hkR ht hkS⟩

/-- A basic set containing infinitely many naturals contains a whole tail
of the real line. -/
lemma exists_tail_of_infinite_natTrace {L : List (PolyCond 1)}
    (hT : {k : ℕ | (fun _ : Fin 1 => (k : ℝ)) ∈ BasicSet L}.Infinite) :
    ∃ R : ℝ, ∀ t : ℝ, R < t → (fun _ : Fin 1 => t) ∈ BasicSet L := by
  induction L with
  | nil => exact ⟨0, fun t _ => by simp⟩
  | cons c L ih =>
      have hc : {k : ℕ | c.holds (fun _ => (k : ℝ))}.Infinite := by
        refine hT.mono ?_
        intro k hk
        exact hk c List.mem_cons_self
      have hL' : {k : ℕ | (fun _ : Fin 1 => (k : ℝ)) ∈ BasicSet L}.Infinite := by
        refine hT.mono ?_
        intro k hk d hd
        exact hk d (List.mem_cons_of_mem c hd)
      obtain ⟨R₁, h1⟩ := eventually_holds_of_infinite_nat c hc
      obtain ⟨R₂, h2⟩ := ih hL'
      refine ⟨max R₁ R₂, fun t ht d hd => ?_⟩
      rcases List.mem_cons.mp hd with rfl | hd'
      · exact h1 t (lt_of_le_of_lt (le_max_left _ _) ht)
      · exact h2 t (lt_of_le_of_lt (le_max_right _ _) ht) d hd'

/-- **`ℕ` is not semialgebraic**: no finite family of basic pieces unions
to `natSet` — the countability axis of the class is load-bearing, and
this is the named witness the "drop countability" mutant must lose. -/
theorem natSet_not_finiteSA :
    ¬ ∃ (m : ℕ) (L : Fin m → List (PolyCond 1)),
      natSet = ⋃ i, BasicSet (L i) := by
  rintro ⟨m, L, hL⟩
  have hinf : natSet.Infinite :=
    Set.infinite_of_injective_forall_mem
      (f := fun k : ℕ => (fun _ : Fin 1 => (k : ℝ)))
      (fun a b hab => Nat.cast_injective (congrFun hab 0))
      (fun k => ⟨k, rfl⟩)
  obtain ⟨i, hi⟩ : ∃ i, (BasicSet (L i)).Infinite := by
    by_contra hall
    simp only [not_exists, Set.not_infinite] at hall
    exact (hL ▸ hinf) (Set.finite_iUnion hall)
  have hsub : BasicSet (L i) ⊆ natSet :=
    hL ▸ Set.subset_iUnion (fun j => BasicSet (L j)) i
  have htr : {k : ℕ | (fun _ : Fin 1 => (k : ℝ)) ∈ BasicSet (L i)}.Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    have himg : BasicSet (L i) ⊆
        (fun k : ℕ => (fun _ : Fin 1 => (k : ℝ))) ''
          {k : ℕ | (fun _ : Fin 1 => (k : ℝ)) ∈ BasicSet (L i)} := by
      intro x hx
      obtain ⟨k, hk⟩ := hsub hx
      have hxconst : x = fun _ => (k : ℝ) := by rw [eq_const x, hk]
      refine ⟨k, ?_, hxconst.symm⟩
      show (fun _ : Fin 1 => (k : ℝ)) ∈ BasicSet (L i)
      rw [← hxconst]
      exact hx
    exact hi ((hfin.image _).subset himg)
  obtain ⟨R, hR⟩ := exists_tail_of_infinite_natTrace htr
  set t : ℝ := (⌈max R 0⌉₊ : ℝ) + 1 / 2 with ht
  have htR : R < t := by
    have h1 : R ≤ (⌈max R 0⌉₊ : ℝ) :=
      le_trans (le_max_left R 0) (Nat.le_ceil _)
    rw [ht]; linarith
  obtain ⟨k, hk⟩ : (fun _ : Fin 1 => t) ∈ natSet := hsub (hR t htR)
  -- `t = k` puts the natural `k` strictly between consecutive naturals
  have hk' : t = (k : ℝ) := hk
  have h1 : (⌈max R 0⌉₊ : ℝ) < (k : ℝ) := by rw [← hk', ht]; linarith
  have h2 : (k : ℝ) < (⌈max R 0⌉₊ : ℝ) + 1 := by rw [← hk', ht]; linarith
  have h1' : ⌈max R 0⌉₊ < k := Nat.cast_lt.mp h1
  have h2' : k < ⌈max R 0⌉₊ + 1 := by exact_mod_cast h2
  omega

/-! ## Uncountability plumbing for the two remaining refutations -/

lemma exists_uncountable_piece {V : Set (Fin 1 → ℝ)} {m : ℕ}
    (hV : ¬ V.Countable) {F : ℕ → List (PolyCond 1) × PolyMap 1 m}
    (hcov : V ⊆ ⋃ i, BasicSet (F i).1) :
    ∃ i, (V ∩ BasicSet (F i).1).Infinite := by
  have hunc : ∃ i, ¬ (V ∩ BasicSet (F i).1).Countable := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    refine hV (Set.Countable.mono ?_ (Set.countable_iUnion hall))
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hx)
    exact mem_iUnion.mpr ⟨i, hx, hi⟩
  obtain ⟨i, hi⟩ := hunc
  exact ⟨i, fun hfin => hi hfin.countable⟩

lemma not_countable_univ_fin1 : ¬ (Set.univ : Set (Fin 1 → ℝ)).Countable := by
  intro h
  have himg := h.image (fun x : Fin 1 → ℝ => x 0)
  have huniv : (fun x : Fin 1 → ℝ => x 0) '' Set.univ = Set.univ := by
    ext t
    simp only [image_univ, mem_range, mem_univ, iff_true]
    exact ⟨fun _ => t, rfl⟩
  rw [huniv] at himg
  exact Cardinal.not_countable_real himg

/-! ## The `√` pair: graph basic, map not piecewise-polynomial -/

/-- The half-line `[0, ∞)` in `ℝ¹`: one basic piece. -/
def nonnegSet : Set (Fin 1 → ℝ) := BasicSet [⟨-(X 0), .le⟩]

lemma mem_nonnegSet {x : Fin 1 → ℝ} : x ∈ nonnegSet ↔ 0 ≤ x 0 := by
  simp [nonnegSet, PolyCond.holds, neg_nonpos]

lemma not_countable_nonnegSet : ¬ nonnegSet.Countable := by
  intro h
  have himg := h.image (fun x : Fin 1 → ℝ => x 0)
  have hIci : (fun x : Fin 1 → ℝ => x 0) '' nonnegSet = Set.Ici 0 := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_nonnegSet.mp hx
    · intro ht
      exact ⟨fun _ => t, mem_nonnegSet.mpr ht, rfl⟩
  rw [hIci] at himg
  have hIic : (Set.Iic (0 : ℝ)).Countable := by
    have hneg : Set.Iic (0 : ℝ) = Neg.neg '' Set.Ici 0 := by
      ext t
      constructor
      · intro ht
        exact ⟨-t, by simpa using ht, neg_neg t⟩
      · rintro ⟨s, hs, rfl⟩
        simpa using hs
    rw [hneg]
    exact himg.image _
  have : (Set.univ : Set ℝ).Countable := by
    rw [← Set.Iic_union_Ici (a := (0 : ℝ))]
    exact hIic.union himg
  exact Cardinal.not_countable_real this

/-- The square-root map on `[0, ∞)`, valued in the ambient line. -/
def sqrtRaw : nonnegSet → Fin 1 → ℝ := fun x _ => Real.sqrt ((x : Fin 1 → ℝ) 0)

/-- The carving of the square-root graph: one basic piece,
`y² = x ∧ 0 ≤ y`. -/
def sqrtGraphConds : List (PolyCond (1 + 1)) :=
  eqConds (X (Fin.natAdd 1 0) * X (Fin.natAdd 1 0) - X (Fin.castAdd 1 0)) ++
    [⟨-(X (Fin.natAdd 1 0)), .le⟩]

/-- **The graph of `√` is a single basic piece** — so under the
"graph is ω-semialgebraic" reading of *morphism*, `√` would be admitted. -/
theorem graphSet_sqrtRaw_eq_basic :
    graphSet nonnegSet sqrtRaw = BasicSet sqrtGraphConds := by
  ext z
  rw [sqrtGraphConds, basicSet_append]
  constructor
  · rintro ⟨hzV, hzf⟩
    have hb : z (Fin.natAdd 1 0) = Real.sqrt (z (Fin.castAdd 1 0)) :=
      congrFun hzf 0
    have ha : 0 ≤ z (Fin.castAdd 1 0) := mem_nonnegSet.mp hzV
    constructor
    · rw [mem_basicSet_eqConds]
      simp only [map_sub, map_mul, MvPolynomial.aeval_X]
      rw [hb, Real.mul_self_sqrt ha]
      ring
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      show MvPolynomial.aeval z (-(X (Fin.natAdd 1 0))) ≤ 0
      simp only [map_neg, MvPolynomial.aeval_X, neg_nonpos]
      rw [hb]
      exact Real.sqrt_nonneg _
  · rintro ⟨heq, hpos⟩
    rw [mem_basicSet_eqConds] at heq
    simp only [map_sub, map_mul, MvPolynomial.aeval_X, sub_eq_zero] at heq
    have hb : 0 ≤ z (Fin.natAdd 1 0) := by
      have := hpos ⟨-(X (Fin.natAdd 1 0)), .le⟩ (List.mem_singleton.mpr rfl)
      simpa [PolyCond.holds, neg_nonpos] using this
    have ha : 0 ≤ z (Fin.castAdd 1 0) := heq ▸ mul_self_nonneg _
    refine ⟨mem_nonnegSet.mpr ha, ?_⟩
    funext j
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    show z (Fin.natAdd 1 0) = Real.sqrt (z (Fin.castAdd 1 0))
    rw [← heq, Real.sqrt_mul_self hb]

/-- The square-root graph is ω-semialgebraic. -/
theorem isOmegaSA_graphSet_sqrtRaw : IsOmegaSA (graphSet nonnegSet sqrtRaw) := by
  rw [graphSet_sqrtRaw_eq_basic]
  exact IsOmegaSA.of_basic _

/-- **`√` is not countably-piecewise-polynomial**: a polynomial agreeing
with `√` on an infinite set squares to `X`, impossible by degree parity.
Together with `graphSet_sqrtRaw_eq_basic` this separates the two candidate
morphism definitions; the piecewise one composes by substitution and is
the one the category uses. -/
theorem sqrt_not_piecewisePoly : ¬ IsPiecewisePolyOn nonnegSet sqrtRaw := by
  rintro ⟨F, hcov, hagree⟩
  obtain ⟨i, hinter⟩ := exists_uncountable_piece not_countable_nonnegSet hcov
  have hT : ((fun x : Fin 1 → ℝ => x 0) ''
      (nonnegSet ∩ BasicSet (F i).1)).Infinite :=
    hinter.image (fun x _ y _ hxy => by rw [eq_const x, eq_const y, hxy])
  have hpoly : realUni ((F i).2 0) ^ 2 = Polynomial.X := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine hT.mono ?_
    rintro t ⟨x, ⟨hxV, hxB⟩, rfl⟩
    have hag := hagree i ⟨x, hxV⟩ hxB
    have h0 : Real.sqrt (x 0) = MvPolynomial.aeval x ((F i).2 0) := congrFun hag 0
    have heval : (realUni ((F i).2 0)).eval (x 0) = Real.sqrt (x 0) := by
      rw [eval_realUni, ← eq_const x]
      exact h0.symm
    simp only [mem_setOf_eq, Polynomial.eval_pow, Polynomial.eval_X, heval]
    rw [Real.sq_sqrt (mem_nonnegSet.mp hxV)]
  have hq0 : realUni ((F i).2 0) ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hpoly
    exact Polynomial.X_ne_zero hpoly.symm
  have hdeg := congrArg Polynomial.natDegree hpoly
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X] at hdeg
  omega

/-! ## Cubing: monic, epic, not an isomorphism -/

/-- The full line as an object (reducible, so that `Fin realObj.dim`
literals and instances resolve through the definition). -/
abbrev realObj : OmegaSA := ⟨1, Set.univ, IsOmegaSA.univ⟩

/-- The cubing endomorphism of the line. -/
def cubeHom : realObj ⟶ realObj where
  toFun := fun x => ⟨fun _ => (x.1 0) ^ 3, mem_univ _⟩
  property :=
    ⟨fun _ => ([], fun _ : Fin 1 => X 0 ^ 3),
      fun x _ => mem_iUnion.mpr ⟨0, by simp⟩,
      fun _ x _ => funext fun v => by simp [PolyMap.apply, map_pow]⟩

theorem mono_cubeHom : Mono cubeHom := by
  refine OmegaSA.mono_of_injective _ fun u v h => ?_
  have h0 : ((u : Fin 1 → ℝ) 0) ^ 3 = ((v : Fin 1 → ℝ) 0) ^ 3 :=
    congrFun (congrArg Subtype.val h) 0
  have heq := (Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)).injective h0
  exact Subtype.ext (funext fun i => by rw [Subsingleton.elim i 0]; exact heq)

lemma cube_real_surjective (y : ℝ) : ∃ t : ℝ, t ^ 3 = y := by
  rcases le_or_gt 0 y with hy | hy
  · refine ⟨y ^ ((3 : ℝ)⁻¹), ?_⟩
    rw [← Real.rpow_natCast (y ^ ((3 : ℝ)⁻¹)) 3, ← Real.rpow_mul hy]
    norm_num
  · refine ⟨-((-y) ^ ((3 : ℝ)⁻¹)), ?_⟩
    rw [Odd.neg_pow (by decide : Odd 3),
      ← Real.rpow_natCast ((-y) ^ ((3 : ℝ)⁻¹)) 3, ← Real.rpow_mul (by linarith)]
    norm_num

theorem epi_cubeHom : Epi cubeHom := by
  refine OmegaSA.epi_of_surjective _ fun y => ?_
  obtain ⟨t, ht⟩ := cube_real_surjective ((y : Fin 1 → ℝ) 0)
  refine ⟨⟨fun _ => t, mem_univ _⟩, ?_⟩
  refine Subtype.ext (funext fun i => ?_)
  rw [Subsingleton.elim i 0]
  rw [eq_const (y : Fin 1 → ℝ)] at *
  exact ht

theorem not_isIso_cubeHom : ¬ IsIso cubeHom := by
  intro hiso
  obtain ⟨g, hgf, hfg⟩ := OmegaSA.isIso_inverse cubeHom
  obtain ⟨G, hcov, hagree⟩ := g.property
  obtain ⟨i, hinter⟩ := exists_uncountable_piece not_countable_univ_fin1 hcov
  have hT : ((fun x : Fin 1 → ℝ => x 0) ''
      (Set.univ ∩ BasicSet (G i).1)).Infinite :=
    hinter.image (fun x _ y _ hxy => by rw [eq_const x, eq_const y, hxy])
  have hpoly : realUni ((G i).2 0) ^ 3 = Polynomial.X := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine hT.mono ?_
    rintro t ⟨x, ⟨hxV, hxB⟩, rfl⟩
    have hag := hagree i ⟨x, hxV⟩ hxB
    have h0 : ((g.toFun ⟨x, hxV⟩ : Fin 1 → ℝ) 0) =
        MvPolynomial.aeval x ((G i).2 0) := congrFun hag 0
    have hcube : ((g.toFun ⟨x, hxV⟩ : Fin 1 → ℝ) 0) ^ 3 = x 0 := by
      have := congrFun (congrArg Subtype.val (hfg ⟨x, hxV⟩)) 0
      simpa [cubeHom] using this
    have heval : (realUni ((G i).2 0)).eval (x 0) =
        ((g.toFun ⟨x, hxV⟩ : Fin 1 → ℝ) 0) := by
      rw [eval_realUni, ← eq_const x]
      exact h0.symm
    simp only [mem_setOf_eq, Polynomial.eval_pow, Polynomial.eval_X, heval, hcube]
  have hq0 : realUni ((G i).2 0) ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at hpoly
    exact Polynomial.X_ne_zero hpoly.symm
  have hdeg := congrArg Polynomial.natDegree hpoly
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X] at hdeg
  omega

/-- **The category is not balanced**: cubing is monic and epic but not
invertible — so monos are richer than ω-semialgebraic subset inclusions
(the subobject `x³ : ℝ ↪ ℝ` has full set-image yet is not the identity
subobject), and the category is in particular not a topos. -/
theorem omegaSA_not_balanced :
    ∃ (V W : OmegaSA) (f : V ⟶ W), Mono f ∧ Epi f ∧ ¬ IsIso f :=
  ⟨realObj, realObj, cubeHom, mono_cubeHom, epi_cubeHom, not_isIso_cubeHom⟩

end

end SuFunctor.StateSpace
