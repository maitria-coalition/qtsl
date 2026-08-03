import Qtsl.Core.Catalogue

/-!
# Decidable instances for rule applicability (computational core)

`Decidable` instances for the side conditions of the certificate rules,
closing over core Lean only, so the executable checker can decide rule
applicability without mathlib. Proofs avoid mathlib-ecosystem tactics;
all instances are pure Lean, with no foreign-function decision
procedures on any assurance path.
-/

namespace PPLC

instance decidableExistsOptEq {α : Type _} (o : Option α) (P : α → Prop)
    [DecidablePred P] : Decidable (∃ x, o = some x ∧ P x) :=
  match o with
  | none => isFalse (by rintro ⟨x, hx, _⟩; cases hx)
  | some a =>
    decidable_of_iff (P a)
      ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, hx, hP⟩ => by cases hx; exact hP⟩

instance decidableExistsDtypeShape (o : Option TensorType) (s : Shape) :
    Decidable (∃ δ, o = some ⟨s, δ⟩) :=
  match o with
  | none => isFalse (by rintro ⟨δ, h⟩; cases h)
  | some τ =>
    decidable_of_iff (τ = ⟨s, τ.dtype⟩)
      ⟨fun h => ⟨τ.dtype, by rw [← h]⟩,
       fun ⟨_, h⟩ => by cases h; rfl⟩

instance (b : BowTie) (l r : Term) (F : Formula) :
    Decidable (atomicCompareForm b l r F) :=
  inferInstanceAs (Decidable (F = _))

instance (b : BowTie) (l r : Term) (F : Formula) :
    Decidable (atomicCompareZero b l r F) :=
  inferInstanceAs (Decidable (F = _))

instance (F : Formula) (w : Wire) (t : Term) (F' : Formula) :
    Decidable (substituteInFormula F w t F') :=
  inferInstanceAs (Decidable (F' = _))

instance (t : Term) (s : Simplex) (S : ExtensionSet) (F : Formula) :
    Decidable (barycentricHalfspaceForm t s S F) :=
  inferInstanceAs (Decidable (_ = _))

instance (P : Formula) (arg : Term) (F : Formula) :
    Decidable (applyPredicateToTerm P arg F) :=
  inferInstanceAs (Decidable (F = _))

instance (P : Formula) : Decidable (isConicPredicate P) :=
  inferInstanceAs (Decidable (_ = _))

instance (P : Formula) : Decidable (isConvexPredicate P) :=
  inferInstanceAs (Decidable (_ = true))

instance (P : Formula) : Decidable (isUpwardClosedConicPredicate P) :=
  inferInstanceAs (Decidable (_ = _))

instance (S : ExtensionSet) : Decidable (isExtensionSetEmpty S) :=
  inferInstanceAs (Decidable (∀ v, S.contains v = false))

instance (l r : Term) : Decidable (polynomialCanonicalEq l r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (s : Simplex) (S : ExtensionSet) (d : Nat) (p : Term)
    (P : Formula) : Decidable (allForwardDiffBernCoeffsSatisfyP s S d p P) :=
  inferInstanceAs (Decidable (_ = true))

instance (cc : Term) (pre : Formula) (concl : Term) :
    Decidable (farkasCombinationValid cc pre concl) :=
  inferInstanceAs (Decidable (_ = true))

instance (cc : Term) (comps : List Sequent) (pre : Formula)
    (concl : Term) : Decidable (syzygyCombinationValid cc comps pre concl) :=
  inferInstanceAs (Decidable (_ = true))

instance (tX : Term) (s : Simplex) (S : ExtensionSet) (n : Nat)
    (bSimp : Fin n → Simplex) (bS : Fin n → ExtensionSet) (c : Term) :
    Decidable (coverInfeasibilityValid tX s S n bSimp bS c) :=
  inferInstanceAs (Decidable (_ = true))

instance (h p : Wire) (α β γ δ : Rat) (F : Formula) :
    Decidable (lirpaConclusionForm h p α β γ δ F) :=
  inferInstanceAs (Decidable (F = _))

instance (schema : SimpC) (t : Term) (k : Fin schema.cells.length)
    (F : Formula) : Decidable (cellStrictInteriorForm schema t k F) :=
  inferInstanceAs (Decidable (_ = _))

instance (schema : SimpC) (os : List Wire) (k : Fin schema.cells.length)
    (F : Formula) : Decidable (cellOneHotForm schema os k F) :=
  inferInstanceAs (Decidable (_ = _))

instance (schema : SimpC) (t : Term) (k : Fin schema.cells.length)
    (w : Fin schema.nVertices) (F : Formula) :
    Decidable (cellOutWitnessForm schema t k w F) :=
  inferInstanceAs (Decidable (_ = _))

instance (schema : SimpC) (os : List Wire) (k : Fin schema.cells.length)
    (F : Formula) : Decidable (cellOutZeroForm schema os k F) :=
  inferInstanceAs (Decidable (_ = _))

instance (H : Hypernet) (a b : Wire) : Decidable (reluLinked H a b) :=
  inferInstanceAs (Decidable (_ = true))

instance (H : Hypernet) (t u : Term) :
    Decidable (∃ s, t.bshape H = some s ∧ u.bshape H = some s) :=
  match ht : t.bshape H with
  | none => isFalse (by
      rintro ⟨s, hs, _⟩
      cases hs)
  | some s =>
    decidable_of_iff (u.bshape H = some s)
      ⟨fun h => ⟨s, rfl, h⟩, fun ⟨s', hs', hu⟩ => by
        injection hs' with h'
        rw [← h'] at hu
        exact hu⟩

instance (H : Hypernet) (t : Term) :
    Decidable (∃ s, t.bshape H = some s) :=
  decidable_of_iff (t.bshape H).isSome Option.isSome_iff_exists

instance (H : Hypernet) (t : Term) : Decidable (t.finWires H) :=
  inferInstanceAs (Decidable (∀ w ∈ t.freeWires, ∃ τ,
    H.wireType w = some τ ∧ τ.dtype.ext = Ext.fin))

instance (tX : Term) (fw : List Wire) :
    Decidable (∃ w, tX = Term.var w ∧ fw ⊆ [w]) :=
  decidable_of_iff (∃ w, tX.varHead? = some w ∧ fw ⊆ [w])
    (by
      constructor
      · rintro ⟨w, hw, hsub⟩
        exact ⟨w, Term.varHead?_eq_some.mp hw, hsub⟩
      · rintro ⟨w, hw, hsub⟩
        exact ⟨w, Term.varHead?_eq_some.mpr hw, hsub⟩)

instance (apps : List PrimApp) : Decidable (Linearity apps) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (apps : List PrimApp) : Decidable (Acyclic apps) :=
  inferInstanceAs
    (Decidable (∀ i : Fin apps.length, ∀ w ∈ apps[i].inputWires,
      ∀ j : Fin apps.length, w ∈ apps[j].outputWires → j < i))

instance (src dst : Shape) : Decidable (src.broadcastsTo dst) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (wt : Wire → Option TensorType) (app : PrimApp) :
    Decidable (app.TypeConsistent wt) := by
  cases app <;> (simp only [PrimApp.TypeConsistent]; infer_instance)

instance (wt : Wire → Option TensorType) (apps : List PrimApp) :
    Decidable (TypeConsistentAll wt apps) :=
  inferInstanceAs (Decidable (∀ app ∈ apps, app.TypeConsistent wt))

def Formula.decWellTyped (H : Hypernet) :
    (F : Formula) → Decidable (F.WellTyped H)
  | .atom _ l r =>
    inferInstanceAs
      (Decidable (∃ τ, l.type H = some τ ∧ r.type H = some τ))
  | .inRegion t s S =>
    inferInstanceAs
      (Decidable ((∃ τ, t.type H = some τ ∧
        τ.shape = [s.complex.ambDim]) ∧ S.simplex = s))
  | .and l r =>
    haveI := Formula.decWellTyped H l
    haveI := Formula.decWellTyped H r
    inferInstanceAs (Decidable (l.WellTyped H ∧ r.WellTyped H))
  | .or l r =>
    haveI := Formula.decWellTyped H l
    haveI := Formula.decWellTyped H r
    inferInstanceAs (Decidable (l.WellTyped H ∧ r.WellTyped H))
  | .tt => isTrue trivial
  | .ff => isTrue trivial

instance (H : Hypernet) (F : Formula) : Decidable (F.WellTyped H) :=
  Formula.decWellTyped H F

instance (H : Hypernet) (seq : Sequent) : Decidable (seq.wellScoped H) :=
  decidable_of_iff
    (∀ w ∈ seq.pre.freeWires ++ seq.post.freeWires, (H.wireType w).isSome)
    ⟨fun h w hw => h w (List.mem_append.mpr hw),
     fun h w hw => h w (List.mem_append.mp hw)⟩

def PrimApp.isCellApp (s : SimpC) (i : Wire) (os : List Wire) :
    PrimApp → Bool
  | .cell s' i' os' => decide (s = s') && decide (i = i') && decide (os = os')
  | _ => false

theorem PrimApp.isCellApp_iff {s : SimpC} {i : Wire} {os : List Wire}
    {a : PrimApp} : PrimApp.isCellApp s i os a = true ↔ .cell s i os = a := by
  cases a <;>
    simp only [PrimApp.isCellApp, Bool.and_eq_true, decide_eq_true_eq,
      Bool.false_eq_true, PrimApp.cell.injEq, and_assoc,
      reduceCtorEq] <;>
    intro h <;> exact PrimApp.noConfusion h

instance (s : SimpC) (i : Wire) (os : List Wire) (apps : List PrimApp) :
    Decidable (PrimApp.cell s i os ∈ apps) :=
  decidable_of_iff (apps.any (PrimApp.isCellApp s i os)) (by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨a, ha, hp⟩
      exact (PrimApp.isCellApp_iff.mp hp) ▸ ha
    · intro hmem
      exact ⟨_, hmem, PrimApp.isCellApp_iff.mpr rfl⟩)

end PPLC
