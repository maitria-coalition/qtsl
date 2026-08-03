import SuFunctor.StateSpace.Category
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-! # Finite limits in the ω-semialgebraic category

The concrete category of ω-semialgebraic spaces has **all finite limits**,
assembled the classical way:

* a terminal object (`unitObj`: the one point of `ℝ⁰`) and an initial
  object (`emptyObj`);
* binary products (`prodObj`): the product of carriers inside
  `ℝ^(n+m)`, carved by renaming each factor's carving into its block of
  coordinates — products of pieces are pieces;
* equalizers (`eqObj`): the agreement locus, ω-semialgebraic by
  `IsOmegaSA.eqLocus` — per piece-pair, `f = g` is finitely many
  polynomial equations, so the equalizer is carved, not projected;
* `HasFiniteLimits` by equalizers + finite products.

The corestriction step in the equalizer's universal property is free by
design: the piecewise-polynomial property mentions no codomain carving,
so a cone map factors through the agreement locus with its witness
family unchanged.
-/

namespace SuFunctor.StateSpace

open MvPolynomial Set CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## Pairing plumbing: `ℝⁿ × ℝᵐ = ℝ^(n+m)` -/

section Pairing

variable {k n m : ℕ}

/-- Glue a point of `ℝⁿ` and a point of `ℝᵐ` into a point of `ℝ^(n+m)`. -/
def pairFun (a : Fin n → ℝ) (b : Fin m → ℝ) : Fin (n + m) → ℝ :=
  Fin.addCases a b

@[simp] lemma pairFun_castAdd (a : Fin n → ℝ) (b : Fin m → ℝ) (i : Fin n) :
    pairFun a b (Fin.castAdd m i) = a i := by
  simp [pairFun]

@[simp] lemma pairFun_natAdd (a : Fin n → ℝ) (b : Fin m → ℝ) (j : Fin m) :
    pairFun a b (Fin.natAdd n j) = b j := by
  simp [pairFun]

/-- Glue two polynomial maps into a map to the product ambient. -/
def pairPoly (P : PolyMap k n) (Q : PolyMap k m) : PolyMap k (n + m) :=
  Fin.addCases P Q

@[simp] lemma pairPoly_apply (P : PolyMap k n) (Q : PolyMap k m) (x : Fin k → ℝ) :
    (pairPoly P Q).apply x = pairFun (P.apply x) (Q.apply x) := by
  funext v
  refine Fin.addCases (fun i => ?_) (fun j => ?_) v <;>
    simp [pairPoly, pairFun, PolyMap.apply]

end Pairing

/-! ## Terminal and initial objects -/

/-- The terminal object: the unique point of `ℝ⁰`. -/
def unitObj : OmegaSA := ⟨0, Set.univ, IsOmegaSA.univ⟩

instance (V : OmegaSA) : Unique (V ⟶ unitObj) where
  default :=
    { toFun := fun _ => ⟨fun i => i.elim0, mem_univ _⟩
      property := ⟨fun _ => ([], fun j => j.elim0),
        fun x _ => mem_iUnion.mpr ⟨0, by simp⟩,
        fun _ _ _ => funext fun j => j.elim0⟩ }
  uniq f := OmegaSA.hom_ext' fun x => Subtype.ext (funext fun i => i.elim0)

instance : HasTerminal OmegaSA := hasTerminal_of_unique unitObj

/-- The initial object: the empty subset of `ℝ⁰`. -/
def emptyObj : OmegaSA := ⟨0, ∅, IsOmegaSA.empty⟩

instance (V : OmegaSA) : Unique (emptyObj ⟶ V) where
  default :=
    { toFun := fun x => absurd x.2 (Set.notMem_empty _)
      property := ⟨fun _ => ([], fun _ => 0),
        fun _ hx => absurd hx (Set.notMem_empty _),
        fun _ x => absurd x.2 (Set.notMem_empty _)⟩ }
  uniq f := OmegaSA.hom_ext' fun x => absurd x.2 (Set.notMem_empty _)

instance : HasInitial OmegaSA := hasInitial_of_unique emptyObj

/-! ## Binary products -/

section Products

variable (V W : OmegaSA)

/-- The binary product carrier: the product of the carriers inside the
sum of the ambients. -/
def prodCarrier : Set (Fin (V.dim + W.dim) → ℝ) :=
  {z | (fun i => z (Fin.castAdd W.dim i)) ∈ V.carrier ∧
    (fun j => z (Fin.natAdd V.dim j)) ∈ W.carrier}

lemma mem_prodCarrier {z : Fin (V.dim + W.dim) → ℝ} :
    z ∈ prodCarrier V W ↔ (fun i => z (Fin.castAdd W.dim i)) ∈ V.carrier ∧
      (fun j => z (Fin.natAdd V.dim j)) ∈ W.carrier :=
  Iff.rfl

lemma isOmegaSA_prodCarrier : IsOmegaSA (prodCarrier V W) := by
  obtain ⟨F, hF⟩ := V.isOmegaSA
  obtain ⟨G, hG⟩ := W.isOmegaSA
  have h1 : IsOmegaSA {z : Fin (V.dim + W.dim) → ℝ |
      (fun i => z (Fin.castAdd W.dim i)) ∈ V.carrier} := by
    refine ⟨fun i => (F i).map (PolyCond.renameL · W.dim), ?_⟩
    ext z
    simp only [mem_setOf_eq, mem_iUnion]
    rw [hF]
    simp only [mem_iUnion]
    exact exists_congr fun i => (basicSet_map_renameL (F i) z).symm
  have h2 : IsOmegaSA {z : Fin (V.dim + W.dim) → ℝ |
      (fun j => z (Fin.natAdd V.dim j)) ∈ W.carrier} := by
    refine ⟨fun j => (G j).map (PolyCond.renameR · V.dim), ?_⟩
    ext z
    simp only [mem_setOf_eq, mem_iUnion]
    rw [hG]
    simp only [mem_iUnion]
    exact exists_congr fun j => (basicSet_map_renameR (G j) z).symm
  exact h1.inter h2

/-- The binary product object, carved blockwise. -/
def prodObj : OmegaSA :=
  ⟨V.dim + W.dim, prodCarrier V W, isOmegaSA_prodCarrier V W⟩

/-- First projection. -/
def prodFst : prodObj V W ⟶ V where
  toFun := fun z => ⟨fun i => z.1 (Fin.castAdd W.dim i), z.2.1⟩
  property :=
    ⟨fun _ => ([], fun i => X (Fin.castAdd W.dim i)),
      fun x _ => mem_iUnion.mpr ⟨0, by simp⟩,
      fun _ z _ => funext fun i =>
        (aeval_X (R := ℚ) z.1 (Fin.castAdd W.dim i)).symm⟩

/-- Second projection. -/
def prodSnd : prodObj V W ⟶ W where
  toFun := fun z => ⟨fun j => z.1 (Fin.natAdd V.dim j), z.2.2⟩
  property :=
    ⟨fun _ => ([], fun j => X (Fin.natAdd V.dim j)),
      fun x _ => mem_iUnion.mpr ⟨0, by simp⟩,
      fun _ z _ => funext fun j =>
        (aeval_X (R := ℚ) z.1 (Fin.natAdd V.dim j)).symm⟩

variable {V W}

/-- Pairing into the product. -/
def prodLift {U : OmegaSA} (f : U ⟶ V) (g : U ⟶ W) : U ⟶ prodObj V W where
  toFun := fun u =>
    ⟨pairFun (f.toFun u : Fin V.dim → ℝ) (g.toFun u : Fin W.dim → ℝ),
      ⟨by simpa using (f.toFun u).2, by simpa using (g.toFun u).2⟩⟩
  property := by
    obtain ⟨F, hFcov, hFagree⟩ := f.property
    obtain ⟨G, hGcov, hGagree⟩ := g.property
    refine ⟨fun p =>
      ((F (Nat.pairEquiv.symm p).1).1 ++ (G (Nat.pairEquiv.symm p).2).1,
        pairPoly (F (Nat.pairEquiv.symm p).1).2 (G (Nat.pairEquiv.symm p).2).2),
      ?_, ?_⟩
    · intro y hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hFcov hy)
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hGcov hy)
      refine mem_iUnion.mpr ⟨Nat.pairEquiv (i, j), ?_⟩
      simp only [Equiv.symm_apply_apply, basicSet_append, mem_inter_iff]
      exact ⟨hi, hj⟩
    · intro p x hx
      rw [basicSet_append, mem_inter_iff] at hx
      change _ = (pairPoly (F (Nat.pairEquiv.symm p).1).2
        (G (Nat.pairEquiv.symm p).2).2).apply (x : Fin U.dim → ℝ)
      rw [pairPoly_apply]
      exact congrArg₂ pairFun (hFagree _ x hx.1) (hGagree _ x hx.2)

@[simp] lemma prodLift_fst {U : OmegaSA} (f : U ⟶ V) (g : U ⟶ W) :
    prodLift f g ≫ prodFst V W = f := by
  refine OmegaSA.hom_ext' fun u => Subtype.ext (funext fun i => ?_)
  simp [prodLift, prodFst, OmegaSA.comp_toFun]

@[simp] lemma prodLift_snd {U : OmegaSA} (f : U ⟶ V) (g : U ⟶ W) :
    prodLift f g ≫ prodSnd V W = g := by
  refine OmegaSA.hom_ext' fun u => Subtype.ext (funext fun j => ?_)
  simp [prodLift, prodSnd, OmegaSA.comp_toFun]

variable (V W)

/-- The product fan. -/
def prodFan : BinaryFan V W := BinaryFan.mk (prodFst V W) (prodSnd V W)

/-- The product fan is a limit: the census's finite-products entry. -/
def prodFanIsLimit : IsLimit (prodFan V W) := by
  refine BinaryFan.IsLimit.mk _ (fun f g => prodLift f g)
    (fun f g => prodLift_fst f g) (fun f g => prodLift_snd f g) ?_
  intro T f g M hf hg
  refine OmegaSA.hom_ext' fun u => Subtype.ext (funext fun v => ?_)
  refine Fin.addCases (fun i => ?_) (fun j => ?_) v
  · have := congrArg (fun k => ((OmegaSA.Hom.toFun k u : V) : Fin V.dim → ℝ) i) hf
    simpa [prodFan, BinaryFan.mk_fst, prodFst, prodLift, OmegaSA.comp_toFun]
      using this
  · have := congrArg (fun k => ((OmegaSA.Hom.toFun k u : W) : Fin W.dim → ℝ) j) hg
    simpa [prodFan, BinaryFan.mk_snd, prodSnd, prodLift, OmegaSA.comp_toFun]
      using this

instance : HasLimit (pair V W) := HasLimit.mk ⟨prodFan V W, prodFanIsLimit V W⟩

end Products

instance : HasBinaryProducts OmegaSA := hasBinaryProducts_of_hasLimit_pair _

instance : HasFiniteProducts OmegaSA := hasFiniteProducts_of_has_binary_and_terminal

/-! ## Equalizers -/

section Equalizers

variable {V W : OmegaSA} (f g : V ⟶ W)

/-- The equalizer object: the agreement locus, ω-semialgebraic because
per piece-pair it is carved by the polynomial equations `Pᵢ = Qⱼ`. -/
def eqObj : OmegaSA where
  dim := V.dim
  carrier := eqLocus V.carrier
    (fun x => (f.toFun x : Fin W.dim → ℝ)) (fun x => (g.toFun x : Fin W.dim → ℝ))
  isOmegaSA := IsOmegaSA.eqLocus V.isOmegaSA f.property g.property

/-- The equalizer inclusion. -/
def eqInclusion : eqObj f g ⟶ V where
  toFun := fun x => ⟨x.1, x.2.choose⟩
  property := IsPiecewisePolyOn.id _

lemma eqInclusion_condition : eqInclusion f g ≫ f = eqInclusion f g ≫ g := by
  refine OmegaSA.hom_ext' fun x => Subtype.ext ?_
  have h := x.2.choose_spec
  simpa [OmegaSA.comp_toFun, eqInclusion] using h

/-- The equalizer fork. -/
def eqFork : Fork f g := Fork.ofι (eqInclusion f g) (eqInclusion_condition f g)

/-- The equalizer fork is a limit: the census's equalizer entry.  The
lift is the corestriction, whose piecewise witness is the cone map's own
(the map property mentions no codomain). -/
def eqForkIsLimit : IsLimit (eqFork f g) := by
  refine Fork.IsLimit.mk _ (fun s => ?_) (fun s => ?_) (fun s m hm => ?_)
  · -- lift
    refine ⟨fun u => ⟨(s.ι.toFun u : Fin V.dim → ℝ), (s.ι.toFun u).2, ?_⟩, s.ι.property⟩
    have := congrArg (fun k => ((OmegaSA.Hom.toFun k u : W) : Fin W.dim → ℝ)) s.condition
    simpa [OmegaSA.comp_toFun] using this
  · -- fac
    exact OmegaSA.hom_ext' fun u =>
      Subtype.ext (by simp [OmegaSA.comp_toFun, eqFork, eqInclusion])
  · -- uniq
    refine OmegaSA.hom_ext' fun u => Subtype.ext (funext fun v => ?_)
    have := congrArg
      (fun k => ((OmegaSA.Hom.toFun k u : V) : Fin V.dim → ℝ) v) hm
    simpa [eqFork, eqInclusion, OmegaSA.comp_toFun] using this

instance : HasLimit (parallelPair f g) := HasLimit.mk ⟨eqFork f g, eqForkIsLimit f g⟩

end Equalizers

instance : HasEqualizers OmegaSA := hasEqualizers_of_hasLimit_parallelPair _

/-- **The finite-limits census entry**: the ω-semialgebraic category has
all finite limits — terminal object, binary products, and equalizers
suffice, and each was constructed by carving (renamed blocks; polynomial
equations), never by projection. -/
instance : HasFiniteLimits OmegaSA :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

end

end SuFunctor.StateSpace
