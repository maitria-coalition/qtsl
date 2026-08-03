import DoubleCat.Virtual.Grothendieck
import DoubleCat.Virtual.Opfibration
import DoubleCat.Grothendieck

/-!
# Restriction of span-valued lax double functors to the virtual level

A span-valued lax double functor on a pseudo double category `C`
(`SpanValued`, the indexing notion of `DoubleCat.Grothendieck`) restricts
to a span-valued *virtual* indexing (`VSpanValued`, the indexing notion of
`DoubleCat.Virtual.Grothendieck`) on the underlying virtual double
category of `C`: the functor and the loose action are unchanged, and the
action on a multicell — which over a pseudo base is a cell out of the fold
of the domain path — is the lax cell action precomposed with the canonical
comparison `foldLax` from the fold of the mapped path to the value on the
fold, built from the laxators by recursion on the path.  This is the easy
direction of the correspondence between span-valued lax double functors on
a pseudo double category and functors of virtual double categories out of
its underlying virtual double category (Cruttwell–Shulman, "A unified
framework for generalized multicategories", 2010, §9): virtuality absorbs
the laxators, so no comparison data survives in the restricted functor.

The two double categories of elements then agree stratum by stratum:

* objects and tight arrows agree definitionally
  (`SpanValued.grothendieck_restrictVirtual`,
  `SpanValued.grothendieck_restrictVirtual_hom`) — both totals are
  mathlib's category of elements of the same underlying functor;
* loose arrows correspond componentwise (`SpanValued.restrictLooseEquiv`);
* a multicell of the virtual total over a path corresponds to a cell of
  the pseudo total out of the fold of the corresponding path
  (`SpanValued.stratum1CellEquiv`); the decoration of the folded loose
  arrow is the chained decoration pushed through `foldLax`
  (`SpanValued.foldGLoose_dec`, the one substantive comparison).

References: Cruttwell–Shulman, "A unified framework for generalized
multicategories" (2010); Cruttwell–Lambert–Pronk–Szyld, "Double
fibrations" (2022); Lambert, "Discrete double fibrations" (2021);
Patterson, "Structured and decorated cospans from the viewpoint of double
category theory" (2023).
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct VirtualDoubleCategoryData
  VirtualDoubleCategoryStruct

universe w t v u₁ u w₂ t₂ v₂ u₂

attribute [local instance] VirtualDoubleCategoryStruct.ofPseudo

section CastSrc

variable {D : Type u₂} [Category.{v₂} D] [PseudoDoubleCategoryStruct.{w₂, t₂} D]

/-- Transport a cell along an equality of its loose source (the
loose-boundary companion of `Cell.cast`, which transports tight
boundaries). -/
def PseudoDoubleCategoryStruct.Cell.castSrc {a b c d : D}
    {m m' : PseudoDoubleCategoryStruct.Loose a b}
    {n : PseudoDoubleCategoryStruct.Loose c d} {f : a ⟶ c} {g : b ⟶ d}
    (h : m = m') (α : PseudoDoubleCategoryStruct.Cell m n f g) :
    PseudoDoubleCategoryStruct.Cell m' n f g :=
  h ▸ α

theorem PseudoDoubleCategoryStruct.Cell.castSrc_heq {a b c d : D}
    {m m' : PseudoDoubleCategoryStruct.Loose a b}
    {n : PseudoDoubleCategoryStruct.Loose c d} {f : a ⟶ c} {g : b ⟶ d}
    (h : m = m') (α : PseudoDoubleCategoryStruct.Cell m n f g) :
    α.castSrc h ≍ α := by
  subst h; rfl

@[simp]
theorem PseudoDoubleCategoryStruct.Cell.castSrc_symm_castSrc {a b c d : D}
    {m m' : PseudoDoubleCategoryStruct.Loose a b}
    {n : PseudoDoubleCategoryStruct.Loose c d} {f : a ⟶ c} {g : b ⟶ d}
    (h : m = m') (α : PseudoDoubleCategoryStruct.Cell m n f g) :
    (α.castSrc h).castSrc h.symm = α := by
  subst h; rfl

@[simp]
theorem PseudoDoubleCategoryStruct.Cell.castSrc_castSrc_symm {a b c d : D}
    {m m' : PseudoDoubleCategoryStruct.Loose a b}
    {n : PseudoDoubleCategoryStruct.Loose c d} {f : a ⟶ c} {g : b ⟶ d}
    (h : m = m') (α : PseudoDoubleCategoryStruct.Cell m' n f g) :
    (α.castSrc h.symm).castSrc h = α := by
  subst h; rfl

end CastSrc

variable {C : Type u₁} [Category.{v} C] [PseudoDoubleCategoryStruct.{w, t} C]
  [PseudoDoubleCategory C]

namespace SpanValued

variable (F : SpanValued.{w, t, v, u₁, u} C)

/-- The canonical comparison from the fold of the mapped path to the value
on the fold: the `n`-ary laxator of `F`, built from `laxId` (empty path)
and `laxComp` (cons) by recursion on the path.  Cf. `seqFoldAux`, the same
recursion shape valued in structure cells. -/
def foldLax : ∀ {a b : C}
    (ps : LoosePath (PseudoDoubleCategoryStruct.Loose (C := C)) a b),
    DepSpan.FamCell ((ps.map F.obj fun {_ _} e => F.mapLoose e).fold)
      (F.mapLoose ps.fold) (𝟙 (F.obj a)) (𝟙 (F.obj b))
  | _, _, .nil => F.laxId _
  | _, _, .cons e ps => fun x y s =>
      F.laxComp e ps.fold x y ⟨s.1, s.2.1, foldLax ps s.1 y s.2.2⟩

@[simp] theorem foldLax_nil {a : C} :
    foldLax F
        (.nil : LoosePath (PseudoDoubleCategoryStruct.Loose (C := C)) a a) =
      F.laxId a :=
  rfl

@[simp] theorem foldLax_cons {a m b : C}
    (e : PseudoDoubleCategoryStruct.Loose a m)
    (ps : LoosePath (PseudoDoubleCategoryStruct.Loose (C := C)) m b) :
    foldLax F (.cons e ps) = fun x y s =>
      F.laxComp e ps.fold x y ⟨s.1, s.2.1, foldLax F ps s.1 y s.2.2⟩ :=
  rfl

section CcompCoherence

/-! ### Preservation of substitution: the coherence of `foldLax`

The substitution law of the restricted functor reduces, by
`mapCell_vComp` at elements, to an exchange law between the two fold
interpretations of a covering sequence — `F`'s cell action on the
pseudo-level fold (`seqFoldAux`) against the `DepSpan`-level fold of the
image sequence.  The lemmas of this section are the element-level
toolkit: an inverse-transfer lemma (the element form of
`SpanValued.GCell.dec_inv`), two transport collapses, the compatibility
of `foldLax` with concatenation of paths (`foldLax_comp`: induction on
the left path, consuming `laxComp_leftUnitor` at `nil` and
`laxComp_natural` + `laxComp_assoc` at `cons`), and the exchange law
itself (`mapCell_seqFoldAux_foldLax`: induction on the covering
sequence, consuming `laxId_natural` at `nil` and `laxComp_natural` at
`cons`).  Every `DepSpan` boundary cast vanishes definitionally (proof
irrelevance over the definitional category laws of `Type u`), which is
what keeps the chases finite. -/

/-- Transfer an element identity along a tight-wise invertible globular
cell: the element-level form of `SpanValued.GCell.dec_inv`. -/
private theorem mapCell_inv_apply_heq {a b : C}
    {m n : PseudoDoubleCategoryStruct.Loose a b}
    {χ : PseudoDoubleCategoryStruct.Cell m n (𝟙 a) (𝟙 b)}
    {χ' : PseudoDoubleCategoryStruct.Cell n m (𝟙 a) (𝟙 b)}
    (hinv : χ ≫ᵥ χ' ≍ PseudoDoubleCategoryStruct.vId m)
    {x' : F.obj a} {y' : F.obj b} (x : F.obj a) (y : F.obj b)
    (hx : x' = F.map (𝟙 a) x) (hy : y' = F.map (𝟙 b) y)
    (t : F.mapLoose m x y) {t' : F.mapLoose n x' y'}
    (ht : t' ≍ F.mapCell χ x y t) :
    F.mapCell χ' x' y' t' ≍ t := by
  subst hx; subst hy
  rw [eq_of_heq ht]
  exact DepSpan.FamCell.heq_apply (by simp) (by simp)
    ((F.mapCell_vComp_heq χ χ').symm.trans
      ((F.mapCell_congr_heq (by simp) (by simp) hinv).trans
        (F.mapCell_vId_heq m))) x y t

/-- Evaluating the fold of a domain-transported covering sequence at a
correspondingly transported element (the same collapse as in
`DoubleCat.Virtual.Grothendieck`, restated here for the target). -/
private theorem seqFoldAux_castDom_apply {A₀ B₀ : Type u}
    {qs : LoosePath (PseudoDoubleCategoryStruct.Loose (C := Type u)) A₀ B₀}
    {a' b' : Type u}
    {ps ps' : LoosePath (PseudoDoubleCategoryStruct.Loose (C := Type u)) a' b'}
    {u' : a' ⟶ A₀} {v' : b' ⟶ B₀} (hp : ps = ps')
    (W : CellSeq (C := Type u) qs ps u' v') {x : a'} {y : b'}
    {pt : ps'.fold x y} {pt' : ps.fold x y} (hpt : pt ≍ pt') :
    seqFoldAux (W.castDom hp) x y pt ≍ seqFoldAux W x y pt' := by
  subst hp
  cases eq_of_heq hpt
  rfl

/-- Splitting a heterogeneous equality of composite-span elements whose
tail families agree propositionally (the same splitter as in
`DoubleCat.Virtual.Grothendieck`). -/
private theorem comp_heq_split {A M B : Type u} {Mf : DepSpan.Fam A M}
    {N N' : DepSpan.Fam M B} (hN : N = N') {x : A} {z : B} {y y' : M}
    {m : Mf x y} {m' : Mf x y'} {n : N y z} {n' : N' y' z}
    (h : (⟨y, m, n⟩ : DepSpan.Fam.comp Mf N x z) ≍
        (⟨y', m', n'⟩ : DepSpan.Fam.comp Mf N' x z)) :
    y = y' ∧ m ≍ m' ∧ n ≍ n' := by
  subst hN
  injection eq_of_heq h with h₁ h₂
  subst h₁
  injection eq_of_heq h₂ with h₃ h₄
  exact ⟨rfl, heq_of_eq h₃, heq_of_eq h₄⟩

/-- The canonical fold comparison of the target, ascribed as the
fiberwise map it is over `DepSpan` (the instance projections otherwise
block applying it to elements; the same device appears in
`DoubleCat.Virtual.Grothendieck`). -/
private abbrev fCC {A₀ M₀ B₀ : Type u}
    (X : LoosePath (PseudoDoubleCategoryStruct.Loose (C := Type u)) A₀ M₀)
    (Y : LoosePath (PseudoDoubleCategoryStruct.Loose (C := Type u)) M₀ B₀) :
    ∀ x y, (X.comp Y).fold x y → DepSpan.Fam.comp X.fold Y.fold x y :=
  LoosePath.foldCompCell X Y

/-- Compatibility of `foldLax` with concatenation of paths: `F`'s cell
action on the canonical fold comparison of the base carries the `n`-ary
laxator of a concatenation to the binary compositor of the two `n`-ary
laxators, read at elements through the target's fold comparison.
Induction on the left path: the `nil` case is `laxComp_leftUnitor` at
elements, the `cons` case is `laxComp_natural` and `laxComp_assoc` at
elements. -/
private theorem foldLax_comp :
    ∀ {a m b : C}
      (ps : LoosePath (PseudoDoubleCategoryStruct.Loose (C := C)) a m)
      (rs : LoosePath (PseudoDoubleCategoryStruct.Loose (C := C)) m b)
      (x : F.obj a) (y : F.obj b)
      (s : ((ps.comp rs).map F.obj fun {_ _} e => F.mapLoose e).fold x y)
      (s' : ((ps.map F.obj fun {_ _} e => F.mapLoose e).comp
        (rs.map F.obj fun {_ _} e => F.mapLoose e)).fold x y)
      (_hs : s' ≍ s),
      F.mapCell (LoosePath.foldCompCell ps rs) x y
          (foldLax F (ps.comp rs) x y s)
        ≍ F.laxComp ps.fold rs.fold x y
            ⟨(fCC _ _ x y s').1,
              foldLax F ps x _ (fCC _ _ x y s').2.1,
              foldLax F rs _ y (fCC _ _ x y s').2.2⟩
  | _, _, _, .nil, rs, x, y, s, s', hs => by
      cases eq_of_heq hs.symm
      have hlu :
          F.mapCell (lLeftUnitor rs.fold) x y
              (F.laxComp (𝟙ˡ _) rs.fold x y
                ⟨x, F.laxId _ x x ⟨⟨rfl⟩⟩, foldLax F rs x y s⟩)
            ≍ foldLax F rs x y s :=
        DepSpan.FamCell.heq_apply (by simp) (by simp)
          (F.laxComp_leftUnitor_heq rs.fold) x y
          ⟨x, ⟨⟨rfl⟩⟩, foldLax F rs x y s⟩
      exact mapCell_inv_apply_heq F
        (PseudoDoubleCategory.lLeftUnitor_lLeftUnitorInv_heq rs.fold)
        x y (by simp) (by simp) _ hlu.symm
  | a, m, b, .cons (b := a₁) e ps', rs, x, y, s, s', hs => by
      obtain ⟨m₀, d₀, tl⟩ := s
      obtain ⟨m₀', d₀', tl'⟩ := s'
      obtain ⟨hm, hd, htl⟩ :=
        comp_heq_split
          (congrArg LoosePath.fold
            (LoosePath.map_comp F.obj (fun {_ _} e => F.mapLoose e)
              ps' rs)) hs.symm
      subst hm
      cases eq_of_heq hd
      have hIH := foldLax_comp ps' rs m₀ y tl tl' htl.symm
      -- strip the boundary cast and split the tight-wise composite:
      have h1 :
          F.mapCell (LoosePath.foldCompCell (LoosePath.cons e ps') rs) x y
              (F.laxComp e (ps'.comp rs).fold x y
                ⟨m₀, d₀, foldLax F (ps'.comp rs) m₀ y tl⟩)
            ≍ F.mapCell
                (lAssocInv e ps'.fold rs.fold) (F.map (𝟙 a) x) (F.map (𝟙 b) y)
                (F.mapCell
                  (PseudoDoubleCategoryStruct.vId e ⊚
                    LoosePath.foldCompCell ps' rs) x y
                  (F.laxComp e (ps'.comp rs).fold x y
                    ⟨m₀, d₀, foldLax F (ps'.comp rs) m₀ y tl⟩)) :=
        DepSpan.FamCell.heq_apply (by simp) (by simp)
          ((F.mapCell_congr_heq (by simp) (by simp)
              (PseudoDoubleCategoryStruct.Cell.cast_heq _ _ _)).trans
            (F.mapCell_vComp_heq _ _))
          x y
          (F.laxComp e (ps'.comp rs).fold x y
            ⟨m₀, d₀, foldLax F (ps'.comp rs) m₀ y tl⟩)
      -- naturality of the compositor against `vId ⊚ foldCompCell`, then
      -- the identity cell and the inductive hypothesis at the components:
      have h2a :
          F.mapCell
              (PseudoDoubleCategoryStruct.vId e ⊚
                LoosePath.foldCompCell ps' rs) x y
              (F.laxComp e (ps'.comp rs).fold x y
                ⟨m₀, d₀, foldLax F (ps'.comp rs) m₀ y tl⟩)
            ≍ F.laxComp e (ps'.fold ⊙ rs.fold) x y
                ⟨m₀, d₀,
                  F.laxComp ps'.fold rs.fold m₀ y
                    ⟨(fCC _ _ m₀ y tl').1,
                      foldLax F ps' m₀ _ (fCC _ _ m₀ y tl').2.1,
                      foldLax F rs _ y (fCC _ _ m₀ y tl').2.2⟩⟩ := by
        refine (DepSpan.FamCell.heq_apply (by simp) (by simp)
            (F.laxComp_natural_heq (PseudoDoubleCategoryStruct.vId e)
              (LoosePath.foldCompCell ps' rs)) x y
            ⟨m₀, d₀, foldLax F (ps'.comp rs) m₀ y tl⟩).trans ?_
        exact DepSpan.FamCell.apply_congr_heq
          (F.laxComp e (ps'.fold ⊙ rs.fold)) (by rw [F.map_id]; rfl)
          (by rw [F.map_id]; rfl)
          (DepSpan.comp_heq (by simp) (by simp) (by simp)
            (DepSpan.FamCell.heq_apply (by simp) (by simp)
              (F.mapCell_vId_heq e) x m₀ d₀)
            hIH)
      -- the associativity coherence, read at the element:
      have hassoc :
          F.mapCell (lAssoc e ps'.fold rs.fold) x y
              (F.laxComp (e ⊙ ps'.fold) rs.fold x y
                ⟨(fCC _ _ m₀ y tl').1,
                  F.laxComp e ps'.fold x _
                    ⟨m₀, d₀, foldLax F ps' m₀ _ (fCC _ _ m₀ y tl').2.1⟩,
                  foldLax F rs _ y (fCC _ _ m₀ y tl').2.2⟩)
            ≍ F.laxComp e (ps'.fold ⊙ rs.fold) x y
                ⟨m₀, d₀,
                  F.laxComp ps'.fold rs.fold m₀ y
                    ⟨(fCC _ _ m₀ y tl').1,
                      foldLax F ps' m₀ _ (fCC _ _ m₀ y tl').2.1,
                      foldLax F rs _ y (fCC _ _ m₀ y tl').2.2⟩⟩ :=
        DepSpan.FamCell.heq_apply (by simp) (by simp)
          (F.laxComp_assoc_heq e ps'.fold rs.fold) x y
          ⟨(fCC _ _ m₀ y tl').1,
            ⟨m₀, d₀, foldLax F ps' m₀ _ (fCC _ _ m₀ y tl').2.1⟩,
            foldLax F rs _ y (fCC _ _ m₀ y tl').2.2⟩
      exact (h1.trans
        (DepSpan.FamCell.apply_congr_heq
          (F.mapCell (lAssocInv e ps'.fold rs.fold))
          (by rw [F.map_id]) (by rw [F.map_id]) h2a)).trans
        (mapCell_inv_apply_heq F
          (PseudoDoubleCategory.lAssoc_lAssocInv_heq e ps'.fold rs.fold)
          x y (by rw [F.map_id]) (by rw [F.map_id]) _ hassoc.symm)

/-- The exchange law: `F`'s cell action on the pseudo-level fold of a
covering sequence, read through `foldLax`, is `foldLax` read through the
target-level fold of the image sequence.  Induction on the sequence:
`laxId_natural` at `nil`, `laxComp_natural` threaded through
`foldLax_comp` at `cons`. -/
private theorem mapCell_seqFoldAux_foldLax :
    ∀ {a b c d : C}
      {qs : LoosePath (PseudoDoubleCategoryStruct.Loose (C := C)) c d}
      {ps : LoosePath (PseudoDoubleCategoryStruct.Loose (C := C)) a b}
      {u : a ⟶ c} {v : b ⟶ d} (V : CellSeq (C := C) qs ps u v)
      (x : F.obj a) (y : F.obj b)
      (s : (ps.map F.obj fun {_ _} e => F.mapLoose e).fold x y),
      F.mapCell (seqFoldAux V) x y (foldLax F ps x y s)
        ≍ foldLax F qs (F.map u x) (F.map v y)
            (seqFoldAux
              (mapSeqAux F.obj (fun {_ _} k => F.map k)
                (fun {_ _} e => F.mapLoose e)
                (fun {_ _ _ _ ps _ _ _} α => fun x y t =>
                  F.mapCell α x y (foldLax F ps x y t)) V)
              x y s)
  | _, _, _, _, _, _, _, _, .nil f, x, y, s =>
      DepSpan.FamCell.heq_apply rfl rfl (F.laxId_natural_heq f) x y s
  | _, _, _, _, _, _, _, _,
      .cons (ps₁ := ps₁) (q := q) (u := ut) (w := w) (qs := qs') (rs := rs)
        (v := vt) β V',
      x, y, s => by
      -- the transported copy of the element across `map_comp`:
      have hfold :
          ((ps₁.comp rs).map F.obj fun {_ _} e => F.mapLoose e).fold x y =
            ((ps₁.map F.obj fun {_ _} e => F.mapLoose e).comp
              (rs.map F.obj fun {_ _} e => F.mapLoose e)).fold x y :=
        congrArg
          (fun z : LoosePath (PseudoDoubleCategoryStruct.Loose (C := Type u)) _ _ =>
            LoosePath.fold z x y)
          (LoosePath.map_comp F.obj (fun {_ _} e => F.mapLoose e) ps₁ rs)
      have hss : (cast hfold s : _) ≍ s := cast_heq hfold s
      -- the left side: strip the cast, split the composite, exchange
      -- through `foldLax_comp`, then `laxComp_natural` at the element:
      have h1 :
          F.mapCell (seqFoldAux (CellSeq.cons β V')) x y
              (foldLax F (ps₁.comp rs) x y s)
            ≍ F.mapCell (β ⊚ seqFoldAux V') (F.map (𝟙 _) x) (F.map (𝟙 _) y)
                (F.mapCell (LoosePath.foldCompCell ps₁ rs) x y
                  (foldLax F (ps₁.comp rs) x y s)) :=
        DepSpan.FamCell.heq_apply (by simp) (by simp)
          ((F.mapCell_congr_heq (by simp) (by simp)
              (PseudoDoubleCategoryStruct.Cell.cast_heq _ _ _)).trans
            (F.mapCell_vComp_heq _ _))
          x y (foldLax F (ps₁.comp rs) x y s)
      have h2 :
          F.mapCell (β ⊚ seqFoldAux V') (F.map (𝟙 _) x) (F.map (𝟙 _) y)
              (F.mapCell (LoosePath.foldCompCell ps₁ rs) x y
                (foldLax F (ps₁.comp rs) x y s))
            ≍ F.mapCell (β ⊚ seqFoldAux V') x y
                (F.laxComp ps₁.fold rs.fold x y
                  ⟨(fCC _ _ x y (cast hfold s)).1,
                    foldLax F ps₁ x _ (fCC _ _ x y (cast hfold s)).2.1,
                    foldLax F rs _ y (fCC _ _ x y (cast hfold s)).2.2⟩) :=
        DepSpan.FamCell.apply_congr_heq (F.mapCell (β ⊚ seqFoldAux V'))
          (by simp) (by simp)
          (foldLax_comp F ps₁ rs x y s (cast hfold s) hss)
      have h3 :
          F.mapCell (β ⊚ seqFoldAux V') x y
              (F.laxComp ps₁.fold rs.fold x y
                ⟨(fCC _ _ x y (cast hfold s)).1,
                  foldLax F ps₁ x _ (fCC _ _ x y (cast hfold s)).2.1,
                  foldLax F rs _ y (fCC _ _ x y (cast hfold s)).2.2⟩)
            ≍ F.laxComp q qs'.fold (F.map ut x) (F.map vt y)
                ⟨F.map w (fCC _ _ x y (cast hfold s)).1,
                  F.mapCell β x _
                    (foldLax F ps₁ x _ (fCC _ _ x y (cast hfold s)).2.1),
                  F.mapCell (seqFoldAux V') _ y
                    (foldLax F rs _ y (fCC _ _ x y (cast hfold s)).2.2)⟩ :=
        DepSpan.FamCell.heq_apply (by simp) (by simp)
          (F.laxComp_natural_heq β (seqFoldAux V')) x y
          ⟨(fCC _ _ x y (cast hfold s)).1,
            foldLax F ps₁ x _ (fCC _ _ x y (cast hfold s)).2.1,
            foldLax F rs _ y (fCC _ _ x y (cast hfold s)).2.2⟩
      -- the inductive hypothesis at the tail component:
      have h4 :
          F.laxComp q qs'.fold (F.map ut x) (F.map vt y)
              ⟨F.map w (fCC _ _ x y (cast hfold s)).1,
                F.mapCell β x _
                  (foldLax F ps₁ x _ (fCC _ _ x y (cast hfold s)).2.1),
                F.mapCell (seqFoldAux V') _ y
                  (foldLax F rs _ y (fCC _ _ x y (cast hfold s)).2.2)⟩
            ≍ F.laxComp q qs'.fold (F.map ut x) (F.map vt y)
                ⟨F.map w (fCC _ _ x y (cast hfold s)).1,
                  F.mapCell β x _
                    (foldLax F ps₁ x _ (fCC _ _ x y (cast hfold s)).2.1),
                  foldLax F qs' _ (F.map vt y)
                    (seqFoldAux
                      (mapSeqAux F.obj (fun {_ _} k => F.map k)
                        (fun {_ _} e => F.mapLoose e)
                        (fun {_ _ _ _ ps _ _ _} α => fun x y t =>
                          F.mapCell α x y (foldLax F ps x y t)) V')
                      _ y (fCC _ _ x y (cast hfold s)).2.2)⟩ :=
        DepSpan.FamCell.apply_congr_heq (F.laxComp q qs'.fold) rfl rfl
          (DepSpan.comp_heq rfl rfl rfl HEq.rfl
            (mapCell_seqFoldAux_foldLax V' _ y
              (fCC _ _ x y (cast hfold s)).2.2))
      -- the right side re-expressed through the domain transport of the
      -- image sequence:
      have h5 :
          foldLax F (LoosePath.cons q qs') (F.map ut x) (F.map vt y)
              (seqFoldAux
                (mapSeqAux F.obj (fun {_ _} k => F.map k)
                  (fun {_ _} e => F.mapLoose e)
                  (fun {_ _ _ _ ps _ _ _} α => fun x y t =>
                    F.mapCell α x y (foldLax F ps x y t))
                  (CellSeq.cons β V'))
                x y s)
            ≍ foldLax F (LoosePath.cons q qs') (F.map ut x) (F.map vt y)
                (seqFoldAux
                  (CellSeq.cons
                    (fun x y t => F.mapCell β x y (foldLax F ps₁ x y t))
                    (mapSeqAux F.obj (fun {_ _} k => F.map k)
                      (fun {_ _} e => F.mapLoose e)
                      (fun {_ _ _ _ ps _ _ _} α => fun x y t =>
                        F.mapCell α x y (foldLax F ps x y t)) V'))
                  x y (cast hfold s)) :=
        DepSpan.FamCell.apply_congr_heq
          (foldLax F (LoosePath.cons q qs')) rfl rfl
          (seqFoldAux_castDom_apply
            (LoosePath.map_comp F.obj (fun {_ _} e => F.mapLoose e)
              ps₁ rs).symm
            _ hss.symm)
      exact (((h1.trans h2).trans h3).trans h4).trans h5.symm

end CcompCoherence

/-- The underlying span-valued virtual indexing of a span-valued lax
double functor: the functor and the loose action are unchanged; the
multicell action is the cell action precomposed with the canonical fold
comparison `foldLax`.  Against the underlying virtual double category of
the target, the laxators are absorbed into the multicell action rather
than carried as separate data (Cruttwell–Shulman, 2010, §9). -/
def restrictVirtual : VSpanValued.{w, t, v, u₁, u} C where
  toFunctor := F.toFunctor
  mapLoose m := F.mapLoose m
  mapCell {a b c d ps q f g} α := fun x y s =>
    F.mapCell α x y (foldLax F ps x y s)
  mapCell_cid q :=
    DepSpan.FamCell.heq_of_apply (by simp) (by simp) fun x y s =>
      DepSpan.FamCell.heq_apply (by simp) (by simp)
        (F.laxComp_rightUnitor_heq q) x y s
  mapCell_ccomp {a b c d e e' qs s f g ps u v} α V :=
    -- Preservation of substitution is the coherence of the `n`-ary
    -- laxator `foldLax` with substitution of covering sequences: by
    -- `mapCell_vComp` at elements it reduces to the exchange law
    -- `mapCell_seqFoldAux_foldLax` above.
    DepSpan.FamCell.heq_of_apply (F.map_comp u f) (F.map_comp v g)
      fun x y t =>
        (DepSpan.FamCell.heq_apply (F.map_comp u f) (F.map_comp v g)
            (F.mapCell_vComp_heq (seqFoldAux V) α) x y
            (foldLax F ps x y t)).trans
          (DepSpan.FamCell.apply_congr_heq (F.mapCell α) rfl rfl
            (mapCell_seqFoldAux_foldLax F V x y t))

section Stratum

/-- Stratum 0, objects: the two double categories of elements have the
same objects — both are mathlib's category of elements of the underlying
functor, definitionally. -/
theorem grothendieck_restrictVirtual :
    VSpanValued.Grothendieck (restrictVirtual F) = Grothendieck F :=
  rfl

/-- Stratum 0, tight arrows: the tight hom-types of the two totals agree
definitionally. -/
theorem grothendieck_restrictVirtual_hom
    (p q : VSpanValued.Grothendieck (restrictVirtual F)) :
    (p ⟶ q) = ((p : Grothendieck F) ⟶ (q : Grothendieck F)) :=
  rfl

/-- Stratum 1, loose arrows: loose arrows of the two totals correspond
componentwise (the base loose arrows and the decoration types agree
definitionally). -/
def restrictLooseEquiv (p q : Grothendieck F) :
    GLoose p q ≃ VSpanValued.VGLoose (P := restrictVirtual F) p q where
  toFun M := ⟨M.base, M.dec⟩
  invFun M := ⟨M.base, M.dec⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The pseudo-total loose arrow underlying a virtual-total loose arrow
(the inverse leg of `restrictLooseEquiv`, named for use in the fold). -/
@[reducible] def toGLoose {p q : Grothendieck F}
    (N : VSpanValued.VGLoose (P := restrictVirtual F) p q) : GLoose p q :=
  ⟨N.base, N.dec⟩

/-- The fold of a path of virtual-total loose arrows in the pseudo total:
the empty path folds to the loose identity, `cons` to the loose
composite.  Its base is the fold of the base path (`foldGLoose_base`) and
its decoration is the chained decoration pushed through the canonical
comparison (`foldGLoose_dec`). -/
def foldGLoose : ∀ {p q : Grothendieck F},
    LoosePath (VSpanValued.VGLoose (P := restrictVirtual F)) p q →
      GLoose p q
  | p, _, .nil => GLoose.id p
  | _, _, .cons e Ξ => (toGLoose F e).comp (foldGLoose Ξ)

@[simp] theorem foldGLoose_nil {p : Grothendieck F} :
    foldGLoose F
        (.nil : LoosePath (VSpanValued.VGLoose (P := restrictVirtual F)) p p) =
      GLoose.id p :=
  rfl

@[simp] theorem foldGLoose_cons {p m q : Grothendieck F}
    (e : VSpanValued.VGLoose (P := restrictVirtual F) p m)
    (Ξ : LoosePath (VSpanValued.VGLoose (P := restrictVirtual F)) m q) :
    foldGLoose F (.cons e Ξ) = (toGLoose F e).comp (foldGLoose F Ξ) :=
  rfl

/-- The base of the fold is the fold of the base path. -/
theorem foldGLoose_base : ∀ {p q : Grothendieck F}
    (Ξ : LoosePath (VSpanValued.VGLoose (P := restrictVirtual F)) p q),
    (foldGLoose F Ξ).base = (VSpanValued.basePath Ξ).fold
  | _, _, .nil => rfl
  | _, _, .cons e Ξ =>
      congrArg (fun m => e.base ⊙ m) (foldGLoose_base Ξ)

/-- Congruence for an application of the compositor in its second loose
argument and the matching component of the element (the recursion step of
`foldGLoose_dec`). -/
theorem laxComp_congr_arg_heq {a m b : C}
    (e : PseudoDoubleCategoryStruct.Loose a m)
    {n n' : PseudoDoubleCategoryStruct.Loose m b} (hn : n = n')
    (x : F.obj a) (z : F.obj m) (y : F.obj b)
    (u : F.mapLoose e x z) {w : F.mapLoose n z y} {w' : F.mapLoose n' z y}
    (hw : w ≍ w') :
    F.laxComp e n x y ⟨z, u, w⟩ ≍ F.laxComp e n' x y ⟨z, u, w'⟩ := by
  subst hn
  rw [eq_of_heq hw]

/-- The decoration of the fold is the chained decoration pushed through
the canonical comparison: the heterogeneous compatibility of `foldGLoose`
with `chainDec` and `foldLax`.  This is the one substantive comparison of
the stratum-1 identification. -/
theorem foldGLoose_dec {p q : Grothendieck F}
    (Ξ : LoosePath (VSpanValued.VGLoose (P := restrictVirtual F)) p q) :
    (foldGLoose F Ξ).dec ≍
      foldLax F (VSpanValued.basePath Ξ) p.2 q.2 (VSpanValued.chainDec Ξ) := by
  induction Ξ with
  | nil => exact HEq.rfl
  | cons e Ξ ih =>
      exact laxComp_congr_arg_heq F e.base (foldGLoose_base F Ξ) _ _ _
        e.dec ih

/-- Applying the cell action to a source-recast cell, at an element
transported accordingly. -/
theorem mapCell_castSrc_apply_heq {a b c d : C}
    {m m' : PseudoDoubleCategoryStruct.Loose a b}
    {n : PseudoDoubleCategoryStruct.Loose c d} {f : a ⟶ c} {g : b ⟶ d}
    (h : m = m') (α : PseudoDoubleCategoryStruct.Cell m n f g)
    (x : F.obj a) (y : F.obj b) {sm : F.mapLoose m' x y}
    {s : F.mapLoose m x y} (hs : sm ≍ s) :
    F.mapCell (α.castSrc h) x y sm ≍ F.mapCell α x y s := by
  subst h
  rw [eq_of_heq hs]
  exact HEq.rfl

variable {F}

/-- Stratum 1, multicells: a multicell of the virtual total over a path
`Ξ` corresponds to a cell of the pseudo total out of the fold of the
corresponding path.  Forward and backward maps carry the same base cell
(recast along `foldGLoose_base`); the decoration conditions transport
along `foldGLoose_dec`. -/
def stratum1CellEquiv {p q r s : Grothendieck F}
    (Ξ : LoosePath (VSpanValued.VGLoose (P := restrictVirtual F)) p q)
    (N : VSpanValued.VGLoose (P := restrictVirtual F) r s)
    (φ : p ⟶ r) (ψ : q ⟶ s) :
    VSpanValued.VGCell Ξ N φ ψ ≃ GCell (foldGLoose F Ξ) (toGLoose F N) φ ψ where
  toFun A :=
    { base := A.base.castSrc (foldGLoose_base F Ξ).symm
      dec :=
        (mapCell_castSrc_apply_heq F (foldGLoose_base F Ξ).symm A.base
            p.2 q.2 (foldGLoose_dec F Ξ)).trans A.dec }
  invFun G :=
    { base := G.base.castSrc (foldGLoose_base F Ξ)
      dec :=
        (mapCell_castSrc_apply_heq F (foldGLoose_base F Ξ) G.base
            p.2 q.2 (foldGLoose_dec F Ξ).symm).trans G.dec }
  left_inv A :=
    VSpanValued.VGCell.ext
      (PseudoDoubleCategoryStruct.Cell.castSrc_castSrc_symm _ A.base)
  right_inv G :=
    GCell.ext (PseudoDoubleCategoryStruct.Cell.castSrc_symm_castSrc _ G.base)

/-- The projection of the decorated total of the restricted indexing is a
discrete virtual double opfibration: together with the stratum
identifications above, the statement of record — a span-valued lax double
functor on a pseudo double category induces a total whose projection lifts
tight arrows and multicells uniquely (Lambert, 2021;
Cruttwell–Lambert–Pronk–Szyld, 2022). -/
theorem restrictVirtual_vproj_isDiscreteOpfibration
    (F : SpanValued.{w, t, v, u₁, u} C) :
    IsDiscreteVirtualDoubleOpfibration
      (VSpanValued.vproj (restrictVirtual F)) :=
  VSpanValued.vproj_isDiscreteOpfibration (P := restrictVirtual F)

end Stratum

end SpanValued

end CategoryTheory
