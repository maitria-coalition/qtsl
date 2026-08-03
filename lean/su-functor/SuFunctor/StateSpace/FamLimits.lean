import SuFunctor.StateSpace.FamCat
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-! # Finite limits in the completion

If `C` has finite limits, so does its free countable coproduct
completion — computed componentwise, with the index bookkeeping carrying
the shape:

* the terminal object is the singleton family of the terminal object;
* the binary product of two families is indexed by the *product* of the
  index types (countable), with componentwise products;
* the equalizer of `f, g : A ⟶ B` is indexed by the subtype of indices
  where the two *reindexings* agree (countable), with componentwise
  equalizers of the transport-aligned parallel pairs;
* `HasFiniteLimits` then follows from equalizers + binary products +
  terminal, exactly as in the base ω-semialgebraic census.

(The general fact this specializes: the free coproduct completion of `C`
has finite limits iff `C` has finite *multi*limits, Diers; a category
with genuine finite limits trivially has finite multilimits, which is
the case consumed here.) -/

namespace SuFunctor.StateSpace

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

namespace FamObj

noncomputable section

/-! ## Terminal object -/

section Terminal

variable [HasTerminal C]

instance (A : FamObj C) : Unique (A ⟶ ySing (⊤_ C)) where
  default := ⟨fun _ => PUnit.unit, fun i => terminal.from (A.X i)⟩
  uniq f := by
    refine Hom.ext' (funext fun i => rfl) (fun i => ?_)
    exact terminal.hom_ext _ _

instance : HasTerminal (FamObj C) := hasTerminal_of_unique (ySing (⊤_ C))

end Terminal

/-! ## Binary products -/

section Products

variable [HasBinaryProducts C] (A B : FamObj C)

/-- The binary product family: product-indexed, componentwise products. -/
@[reducible]
def famProd : FamObj C :=
  ⟨A.ι × B.ι, fun p => A.X p.1 ⨯ B.X p.2⟩

@[simp] lemma famProd_X (p : (famProd A B).ι) :
    (famProd A B).X p = (A.X p.1 ⨯ B.X p.2) := rfl

/-- First projection. -/
def famProdFst : famProd A B ⟶ A :=
  ⟨fun p => p.1, fun p => prod.fst⟩

/-- Second projection. -/
def famProdSnd : famProd A B ⟶ B :=
  ⟨fun p => p.2, fun p => prod.snd⟩

@[simp] lemma famProdFst_r (p : (famProd A B).ι) : (famProdFst A B).r p = p.1 := rfl

@[simp] lemma famProdFst_app (p : (famProd A B).ι) :
    (famProdFst A B).app p = prod.fst := rfl

@[simp] lemma famProdSnd_r (p : (famProd A B).ι) : (famProdSnd A B).r p = p.2 := rfl

@[simp] lemma famProdSnd_app (p : (famProd A B).ι) :
    (famProdSnd A B).app p = prod.snd := rfl

variable {A B}

/-- Pairing into the product family. -/
def famProdLift {T : FamObj C} (f : T ⟶ A) (g : T ⟶ B) : T ⟶ famProd A B :=
  ⟨fun i => (f.r i, g.r i), fun i => prod.lift (f.app i) (g.app i)⟩

@[simp] lemma famProdLift_r {T : FamObj C} (f : T ⟶ A) (g : T ⟶ B) (i : T.ι) :
    (famProdLift f g).r i = (f.r i, g.r i) := rfl

@[simp] lemma famProdLift_app {T : FamObj C} (f : T ⟶ A) (g : T ⟶ B) (i : T.ι) :
    (famProdLift f g).app i = prod.lift (f.app i) (g.app i) := rfl

@[simp] lemma famProdLift_fst {T : FamObj C} (f : T ⟶ A) (g : T ⟶ B) :
    famProdLift f g ≫ famProdFst A B = f :=
  Hom.ext' rfl (fun i =>
    (Category.comp_id _).trans (prod.lift_fst (f.app i) (g.app i)))

@[simp] lemma famProdLift_snd {T : FamObj C} (f : T ⟶ A) (g : T ⟶ B) :
    famProdLift f g ≫ famProdSnd A B = g :=
  Hom.ext' rfl (fun i =>
    (Category.comp_id _).trans (prod.lift_snd (f.app i) (g.app i)))

/-- Any morphism into a product family is the pairing of its two
projections: the eta law, in the clean vocabulary (no fan point). -/
lemma famProdLift_eta {T : FamObj C} (m : T ⟶ famProd A B) :
    famProdLift (m ≫ famProdFst A B) (m ≫ famProdSnd A B) = m := by
  refine Hom.ext' (funext fun i => rfl) (fun i => ?_)
  refine (Category.comp_id _).trans ?_
  refine prod.hom_ext ?_ ?_
  · exact (prod.lift_fst _ _).trans rfl
  · exact (prod.lift_snd _ _).trans rfl

variable (A B)

/-- The product fan. -/
def famProdFan : BinaryFan A B := BinaryFan.mk (famProdFst A B) (famProdSnd A B)

@[simp] lemma famProdFan_fst : (famProdFan A B).fst = famProdFst A B := rfl

@[simp] lemma famProdFan_snd : (famProdFan A B).snd = famProdSnd A B := rfl

/-- The product fan is a limit: binary products in the completion.
(Uniqueness by the eta law: any cone morphism is the pairing of its
composites with the projections.) -/
def famProdFanIsLimit : IsLimit (famProdFan A B) := by
  refine BinaryFan.IsLimit.mk _ (fun f g => famProdLift f g)
    (fun f g => famProdLift_fst f g) (fun f g => famProdLift_snd f g) ?_
  intro T f g m hf hg
  rw [famProdFan_fst] at hf
  rw [famProdFan_snd] at hg
  rw [← hf, ← hg]
  exact (famProdLift_eta m).symm

instance : HasLimit (pair A B) :=
  HasLimit.mk ⟨famProdFan A B, famProdFanIsLimit A B⟩

end Products

instance [HasBinaryProducts C] : HasBinaryProducts (FamObj C) :=
  hasBinaryProducts_of_hasLimit_pair _

instance [HasTerminal C] [HasBinaryProducts C] : HasFiniteProducts (FamObj C) :=
  hasFiniteProducts_of_has_binary_and_terminal

/-! ## Equalizers -/

section Equalizers

variable [HasEqualizers C] {A B : FamObj C} (f g : A ⟶ B)

/-- The equalizer index type: indices where the reindexings agree. -/
abbrev famEqIdx : Type := {i : A.ι // f.r i = g.r i}

/-- The transport-aligned second leg at an agreeing index. -/
@[reducible]
def famEqAligned (i : famEqIdx f g) : A.X i.1 ⟶ B.X (f.r i.1) :=
  g.app i.1 ≫ eqToHom (congrArg B.X i.2.symm)

/-- The equalizer family: componentwise equalizers over the agreeing
indices. -/
@[reducible]
def famEq : FamObj C :=
  ⟨famEqIdx f g, fun i => equalizer (f.app i.1) (famEqAligned f g i)⟩

@[simp] lemma famEq_X (i : (famEq f g).ι) :
    (famEq f g).X i = equalizer (f.app i.1) (famEqAligned f g i) := rfl

/-- The equalizer inclusion. -/
def famEqInclusion : famEq f g ⟶ A :=
  ⟨fun i => i.1, fun i => equalizer.ι (f.app i.1) (famEqAligned f g i)⟩

@[simp] lemma famEqInclusion_r (i : (famEq f g).ι) :
    (famEqInclusion f g).r i = i.1 := rfl

@[simp] lemma famEqInclusion_app (i : (famEq f g).ι) :
    (famEqInclusion f g).app i = equalizer.ι (f.app i.1) (famEqAligned f g i) := rfl

lemma famEqInclusion_condition :
    famEqInclusion f g ≫ f = famEqInclusion f g ≫ g := by
  refine Hom.ext' (funext fun i => i.2) (fun i => ?_)
  show (equalizer.ι (f.app i.1) (famEqAligned f g i) ≫ f.app i.1) ≫ eqToHom _ =
    equalizer.ι (f.app i.1) (famEqAligned f g i) ≫ g.app i.1
  refine (congrArg (fun k => k ≫ eqToHom _)
    (equalizer.condition (f.app i.1) (famEqAligned f g i))).trans ?_
  -- (ι ≫ (g.app ≫ eqToHom h₂)) ≫ eqToHom h₁ = ι ≫ g.app
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (fun k => equalizer.ι (f.app i.1) (famEqAligned f g i) ≫ k) ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (fun k => g.app i.1 ≫ k) (eqToHom_trans _ _)).trans
    (Category.comp_id _)

/-- The equalizer fork. -/
def famEqFork : Fork f g :=
  Fork.ofι (famEqInclusion f g) (famEqInclusion_condition f g)

@[simp] lemma famEqFork_ι : (famEqFork f g).ι = famEqInclusion f g := rfl

/-- The agreeing-index datum of a fork over `f, g`: its reindexing
equalizes the two reindexings. -/
lemma famEq_fork_idx (s : Fork f g) (t : s.pt.ι) :
    f.r (s.ι.r t) = g.r (s.ι.r t) :=
  congrFun (congrArg Hom.r s.condition) t

/-- The componentwise legs of a fork equalize the aligned parallel pair. -/
lemma famEq_fork_app (s : Fork f g) (t : s.pt.ι) :
    s.ι.app t ≫ f.app (s.ι.r t) =
      s.ι.app t ≫ famEqAligned f g ⟨s.ι.r t, famEq_fork_idx f g s t⟩ := by
  have h := Hom.congr_app s.condition t
  simp only [comp_app] at h
  exact h.trans (Category.assoc _ _ _)

/-- The lift of a fork into the equalizer family, in the clean
vocabulary. -/
def famEqLift (s : Fork f g) : s.pt ⟶ famEq f g :=
  ⟨fun t => ⟨s.ι.r t, famEq_fork_idx f g s t⟩,
    fun t => equalizer.lift (s.ι.app t) (famEq_fork_app f g s t)⟩

lemma famEqLift_ι (s : Fork f g) :
    famEqLift f g s ≫ famEqInclusion f g = s.ι :=
  Hom.ext' (funext fun t => rfl) (fun t =>
    (congrArg (fun k => k ≫ eqToHom _) (equalizer.lift_ι _ _)).trans
      (Category.comp_id _))

/-- `eqToHom` transports move across the componentwise equalizer
inclusions (eliminating the index equality makes both transports
identities). -/
private lemma eqToHom_eq_ι {a b : famEqIdx f g} (hab : a = b)
    (hX : (famEq f g).X a = (famEq f g).X b) (hA : A.X a.1 = A.X b.1) :
    eqToHom hX ≫ equalizer.ι (f.app b.1) (famEqAligned f g b) =
      equalizer.ι (f.app a.1) (famEqAligned f g a) ≫ eqToHom hA := by
  subst hab
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The equalizer inclusion is a monomorphism (componentwise, via the
mono equalizer inclusions of `C`; on indices, via subtype injectivity). -/
instance famEqInclusion_mono : Mono (famEqInclusion f g) := by
  constructor
  intro T u v huv
  have hr : u.r = v.r := by
    funext t
    exact Subtype.ext (congrFun (congrArg Hom.r huv) t)
  refine Hom.ext' hr (fun t => ?_)
  have h := Hom.congr_app huv t
  simp only [comp_app, famEqInclusion_app, famEqInclusion_r] at h
  have hrt : u.r t = v.r t := congrFun hr t
  refine (cancel_mono (equalizer.ι (f.app (v.r t).1)
    (famEqAligned f g (v.r t)))).mp ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun k => u.app t ≫ k)
    (eqToHom_eq_ι f g hrt _ (congrArg (fun q : famEqIdx f g => A.X q.1) hrt))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ eqToHom _) h).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (fun k => (v.app t ≫ equalizer.ι (f.app (v.r t).1)
      (famEqAligned f g (v.r t))) ≫ k) (eqToHom_trans _ _)).trans
    (Category.comp_id _)

/-- The equalizer fork is a limit: equalizers in the completion.
(Uniqueness by cancelling the mono inclusion.) -/
def famEqForkIsLimit : IsLimit (famEqFork f g) := by
  refine Fork.IsLimit.mk _ (fun s => famEqLift f g s)
    (fun s => famEqLift_ι f g s) (fun s m hm => ?_)
  refine (cancel_mono (famEqInclusion f g)).mp ?_
  exact hm.trans (famEqLift_ι f g s).symm

instance : HasLimit (parallelPair f g) :=
  HasLimit.mk ⟨famEqFork f g, famEqForkIsLimit f g⟩

end Equalizers

instance [HasEqualizers C] : HasEqualizers (FamObj C) :=
  hasEqualizers_of_hasLimit_parallelPair _

/-- **Finite limits in the completion**: if `C` has finite limits, so
does `FamObj C` — componentwise, with index bookkeeping carrying the
shape. -/
instance [HasFiniteLimits C] : HasFiniteLimits (FamObj C) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

end

end FamObj

end SuFunctor.StateSpace
