import SuFunctor.StateSpace.Limits

/-! # Countable coproducts: the bag pattern

The property that *distinguishes* the ω-semialgebraic category from the
plain semialgebraic one: a countable family of ω-semialgebraic subsets of
a common ambient `ℝⁿ` has a coproduct, realized concretely as the tagged
union in `ℝ^(n+1)` — copy `i` sits over tag coordinate `i`.  This is the
"bag of pieces" pattern of discrete-mode hybrid state spaces: countably
many modes, each an ω-semialgebraic piece, disjointified by an extra
coordinate.  With finitely many pieces this is ordinary; with countably
many it *exits* the semialgebraic class (`ℕ`-shaped tag sets have
infinitely many connected components) while staying ω-semialgebraic —
each slice is the renamed carving of its summand plus one linear tag
equation, and countably many slices of countably many pieces re-index
along `Nat.pairEquiv`.

Scope note: the family shares one ambient dimension.  Families of
*bounded* dimension reduce to this by zero-padding each summand into the
common ambient (an isomorphism onto its image); families of *unbounded*
dimension have no home in any finite-dimensional concrete ambient — the
coproduct's carrier would be a countable union of piecewise-polynomial
images of positive-dimensional pieces inside a fixed `ℝᴺ`, and a
Baire-category argument (some piece of the `ℝ^(N+1)`-summand's injection
has nonempty interior; no continuous injection of an open subset of
`ℝ^(N+1)` into `ℝᴺ` exists) rules that out.  That refutation consumes
invariance-of-domain-class input not currently mechanized; the abstract
(plots-based) ωPAP construction of arXiv:2302.10636 is where
unbounded-dimension coproducts live.
-/

namespace SuFunctor.StateSpace

open MvPolynomial Set CategoryTheory CategoryTheory.Limits

noncomputable section

variable {n : ℕ} (K : ℕ → Set (Fin n → ℝ)) (hK : ∀ i, IsOmegaSA (K i))

/-- The `i`-th tagged slice: copy `i` of the family, over tag value `i`. -/
def taggedSlice (i : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {z | (fun v => z (Fin.castAdd 1 v)) ∈ K i ∧ z (Fin.natAdd n 0) = (i : ℝ)}

/-- The tag condition `z_tag = i`, as carving data. -/
def tagConds (i : ℕ) : List (PolyCond (n + 1)) :=
  eqConds (X (Fin.natAdd n 0) - C ((i : ℕ) : ℚ))

lemma mem_basicSet_tagConds (i : ℕ) (z : Fin (n + 1) → ℝ) :
    z ∈ BasicSet (tagConds (n := n) i) ↔ z (Fin.natAdd n 0) = (i : ℝ) := by
  rw [tagConds, mem_basicSet_eqConds]
  simp [sub_eq_zero, map_natCast]

include hK in
lemma isOmegaSA_taggedSlice (i : ℕ) : IsOmegaSA (taggedSlice K i) := by
  obtain ⟨F, hF⟩ := hK i
  have h1 : IsOmegaSA {z : Fin (n + 1) → ℝ |
      (fun v => z (Fin.castAdd 1 v)) ∈ K i} := by
    refine ⟨fun j => (F j).map (PolyCond.renameL · 1), ?_⟩
    ext z
    simp only [mem_setOf_eq, mem_iUnion]
    rw [hF]
    simp only [mem_iUnion]
    exact exists_congr fun j => (basicSet_map_renameL (F j) z).symm
  have h2 : IsOmegaSA {z : Fin (n + 1) → ℝ | z (Fin.natAdd n 0) = (i : ℝ)} := by
    refine ⟨fun _ => tagConds i, ?_⟩
    ext z
    rw [mem_iUnion (s := fun _ : ℕ => BasicSet (tagConds (n := n) i))]
    constructor
    · intro hz; exact ⟨0, (mem_basicSet_tagConds i z).mpr hz⟩
    · rintro ⟨-, hz⟩; exact (mem_basicSet_tagConds i z).mp hz
  exact h1.inter h2

/-- The coproduct carrier: the union of the tagged slices. -/
def coprodCarrier : Set (Fin (n + 1) → ℝ) :=
  ⋃ i, taggedSlice K i

/-- The coproduct object. -/
def coprodObj : OmegaSA :=
  ⟨n + 1, coprodCarrier K, IsOmegaSA.iUnion (isOmegaSA_taggedSlice K hK)⟩

/-- The summand objects. -/
def summand (i : ℕ) : OmegaSA := ⟨n, K i, hK i⟩

/-- The tag of a point of the coproduct: the (unique) slice index. -/
def tagOf (z : (coprodObj K hK : Type)) : ℕ :=
  (mem_iUnion.mp z.2).choose

lemma mem_taggedSlice_tagOf (z : (coprodObj K hK : Type)) :
    z.1 ∈ taggedSlice K (tagOf K hK z) :=
  (mem_iUnion.mp z.2).choose_spec

lemma tagOf_eq {z : (coprodObj K hK : Type)} {i : ℕ}
    (hz : z.1 ∈ taggedSlice K i) : tagOf K hK z = i := by
  have h1 := (mem_taggedSlice_tagOf K hK z).2
  have h2 := hz.2
  exact Nat.cast_injective (h1.symm.trans h2)

/-- The `i`-th coproduct injection: pair with the tag. -/
def coprodInj (i : ℕ) : summand K hK i ⟶ coprodObj K hK where
  toFun := fun x =>
    ⟨pairFun x.1 (fun _ : Fin 1 => (i : ℝ)),
      mem_iUnion.mpr ⟨i, ⟨by simpa using x.2, by simp⟩⟩⟩
  property := by
    refine ⟨fun _ => ([], pairPoly (PolyMap.id n) fun _ : Fin 1 => C ((i : ℕ) : ℚ)),
      fun x _ => mem_iUnion.mpr ⟨0, by simp⟩, fun j x _ => ?_⟩
    have hconst : PolyMap.apply (n := n) (m := 1)
        (fun _ => C ((i : ℕ) : ℚ)) (x.1 : Fin n → ℝ) =
        fun _ : Fin 1 => ((i : ℕ) : ℝ) := by
      funext v
      show aeval (x.1 : Fin n → ℝ) (C ((i : ℕ) : ℚ)) = ((i : ℕ) : ℝ)
      rw [MvPolynomial.aeval_C]
      exact map_natCast (algebraMap ℚ ℝ) i
    show pairFun (x.1 : Fin n → ℝ) (fun _ : Fin 1 => (i : ℝ)) =
      (pairPoly (PolyMap.id n) fun _ : Fin 1 => C ((i : ℕ) : ℚ)).apply
        (x.1 : Fin n → ℝ)
    rw [pairPoly_apply, PolyMap.apply_id, hconst]
    rfl

lemma coprodInj_tagOf (i : ℕ) (x : (summand K hK i : Type)) :
    tagOf K hK ((coprodInj K hK i).toFun x) = i :=
  tagOf_eq K hK ⟨by simpa [coprodInj] using x.2, by simp [coprodInj]⟩

/-- The raw copairing function: dispatch on the tag. -/
def descFun {T : OmegaSA} (f : ∀ i, summand K hK i ⟶ T)
    (z : (coprodObj K hK : Type)) : (T : Type) :=
  (f (tagOf K hK z)).toFun
    ⟨fun v => z.1 (Fin.castAdd 1 v),
      (mem_taggedSlice_tagOf K hK z).1⟩

/-- Evaluating the copairing on a point of a known slice: the dispatch
lands on that slice's leg. -/
lemma descFun_slice {T : OmegaSA} (f : ∀ i, summand K hK i ⟶ T)
    {z : (coprodObj K hK : Type)} {i : ℕ}
    (hz : z.1 ∈ taggedSlice K i) :
    descFun K hK f z = (f i).toFun
      ⟨fun v => z.1 (Fin.castAdd 1 v), hz.1⟩ := by
  have h : tagOf K hK z = i := tagOf_eq K hK hz
  subst h
  rfl

/-- Copairing out of the coproduct: dispatch on the tag; the pieces are
each cocone leg's pieces, renamed into the front block and pinned to the
leg's tag value. -/
def coprodDesc {T : OmegaSA} (f : ∀ i, summand K hK i ⟶ T) :
    coprodObj K hK ⟶ T where
  toFun := descFun K hK f
  property := by
    have hFs : ∀ i, ∃ F : ℕ → List (PolyCond n) × PolyMap n T.dim,
        (K i ⊆ ⋃ j, BasicSet (F j).1) ∧
        ∀ (j : ℕ) (x : (summand K hK i : Type)),
          x.1 ∈ BasicSet (F j).1 →
            ((f i).toFun x : Fin T.dim → ℝ) = (F j).2.apply x.1 :=
      fun i => (f i).property
    choose Fs hcov hagree using hFs
    refine ⟨fun p =>
      (((Fs (Nat.pairEquiv.symm p).1 (Nat.pairEquiv.symm p).2).1.map
          (PolyCond.renameL · 1)) ++ tagConds (Nat.pairEquiv.symm p).1,
        fun t => rename (Fin.castAdd 1)
          ((Fs (Nat.pairEquiv.symm p).1 (Nat.pairEquiv.symm p).2).2 t)),
      ?_, ?_⟩
    · -- cover
      intro z hz
      obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov i hzi.1)
      refine mem_iUnion.mpr ⟨Nat.pairEquiv (i, j), ?_⟩
      show z ∈ BasicSet
        ((Fs (Nat.pairEquiv.symm (Nat.pairEquiv (i, j))).1
            (Nat.pairEquiv.symm (Nat.pairEquiv (i, j))).2).1.map
          (PolyCond.renameL · 1) ++
          tagConds (Nat.pairEquiv.symm (Nat.pairEquiv (i, j))).1)
      rw [Equiv.symm_apply_apply]
      intro c hc
      rcases List.mem_append.mp hc with hcl | hcr
      · exact (basicSet_map_renameL _ z).mpr hj c hcl
      · exact (mem_basicSet_tagConds _ z).mpr hzi.2 c hcr
    · -- agreement
      intro p x hx
      replace hx : x.1 ∈ BasicSet
          ((Fs (Nat.pairEquiv.symm p).1 (Nat.pairEquiv.symm p).2).1.map
            (PolyCond.renameL · 1) ++ tagConds (Nat.pairEquiv.symm p).1) := hx
      have hxF : x.1 ∈ BasicSet
          ((Fs (Nat.pairEquiv.symm p).1 (Nat.pairEquiv.symm p).2).1.map
            (PolyCond.renameL · 1)) :=
        fun c hc => hx c (List.mem_append.mpr (Or.inl hc))
      have hxTag : x.1 ∈ BasicSet (tagConds (Nat.pairEquiv.symm p).1) :=
        fun c hc => hx c (List.mem_append.mpr (Or.inr hc))
      have hfront : (fun v => x.1 (Fin.castAdd 1 v)) ∈
          BasicSet (Fs (Nat.pairEquiv.symm p).1 (Nat.pairEquiv.symm p).2).1 :=
        (basicSet_map_renameL _ _).mp hxF
      have htag : x.1 (Fin.natAdd n 0) =
          ((Nat.pairEquiv.symm p).1 : ℝ) :=
        (mem_basicSet_tagConds _ _).mp hxTag
      have hslice : x.1 ∈
          taggedSlice K (Nat.pairEquiv.symm p).1 := by
        refine ⟨?_, htag⟩
        have hmem := mem_taggedSlice_tagOf K hK x
        have hi : tagOf K hK x = (Nat.pairEquiv.symm p).1 :=
          Nat.cast_injective (hmem.2.symm.trans htag)
        rw [← hi]
        exact hmem.1
      have hleg := hagree (Nat.pairEquiv.symm p).1 (Nat.pairEquiv.symm p).2
        ⟨fun v => x.1 (Fin.castAdd 1 v), hslice.1⟩ hfront
      show (descFun K hK f x : Fin T.dim → ℝ) = _
      rw [descFun_slice K hK f hslice]
      funext t
      calc ((f (Nat.pairEquiv.symm p).1).toFun _ : Fin T.dim → ℝ) t
          = (Fs (Nat.pairEquiv.symm p).1 (Nat.pairEquiv.symm p).2).2.apply
              (fun v => x.1 (Fin.castAdd 1 v)) t := by
            rw [hleg]; rfl
        _ = aeval (x.1 : Fin (n + 1) → ℝ)
              (rename (Fin.castAdd 1)
                ((Fs (Nat.pairEquiv.symm p).1 (Nat.pairEquiv.symm p).2).2 t)) :=
            (aeval_rename (Fin.castAdd 1) (x.1 : Fin (n + 1) → ℝ)
              ((Fs (Nat.pairEquiv.symm p).1 (Nat.pairEquiv.symm p).2).2 t)).symm

/-- The coproduct cofan. -/
def coprodCofan : Cofan (summand K hK) :=
  Cofan.mk (coprodObj K hK) (coprodInj K hK)

/-- The tagged union is a colimit cofan: **countable coproducts of
same-ambient families exist** — the census's distinguishing YES. -/
def coprodIsColimit : IsColimit (coprodCofan K hK) := by
  refine Cofan.IsColimit.mk _ (fun t => coprodDesc K hK t.inj) (fun t i => ?_)
    (fun t m hm => ?_)
  · -- fac
    refine OmegaSA.hom_ext' fun x => ?_
    have hslice : ((coprodInj K hK i).toFun x).1 ∈ taggedSlice K i :=
      ⟨by simpa [coprodInj] using x.2, by simp [coprodInj]⟩
    show descFun K hK t.inj ((coprodInj K hK i).toFun x) = _
    rw [descFun_slice K hK t.inj hslice]
    exact congrArg (t.inj i).toFun
      (Subtype.ext (funext fun v => by simp [coprodInj]))
  · -- uniq
    refine OmegaSA.hom_ext' fun z => ?_
    have hslice := mem_taggedSlice_tagOf K hK z
    have hz : ((coprodInj K hK (tagOf K hK z)).toFun
        ⟨fun v => z.1 (Fin.castAdd 1 v), hslice.1⟩) = z := by
      refine Subtype.ext (funext fun v => ?_)
      refine Fin.addCases (fun i => ?_) (fun j => ?_) v
      · simp [coprodInj]
      · have h0 : j = 0 := Subsingleton.elim j 0
        subst h0
        simpa [coprodInj] using hslice.2.symm
    have hm' : coprodInj K hK (tagOf K hK z) ≫ m = t.inj (tagOf K hK z) :=
      hm (tagOf K hK z)
    calc m.toFun z
        = m.toFun ((coprodInj K hK (tagOf K hK z)).toFun _) := by rw [hz]
      _ = ((coprodInj K hK (tagOf K hK z)) ≫ m).toFun _ := rfl
      _ = (t.inj (tagOf K hK z)).toFun _ := by rw [hm']
      _ = descFun K hK t.inj z := (descFun_slice K hK t.inj hslice).symm

/-- **Countable coproducts of same-ambient families exist** — the
distinguishing property of the ω-semialgebraic category over the
semialgebraic one (whose tag sets would need infinitely many connected
components; cf. `natSet_not_finiteSA`). -/
theorem hasCoproduct_of_commonAmbient : HasCoproduct (summand K hK) :=
  ⟨⟨⟨coprodCofan K hK, coprodIsColimit K hK⟩⟩⟩

end

end SuFunctor.StateSpace
