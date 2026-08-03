import SuFunctor.Site.Tangency
import QtslAux.JumpDiffusion

/-! # Family tangencies: step, kernel, and the powerset ENCODING

The family fibration over `Type u` — fibres are point-indexed families
`S → Type u`, reindexing is precomposition — carries the three cheap
tangencies of Capucci–Myers' §2 catalogue at the discrete stratum:

* the **step tangency** `T_s S := S` (their "basic" Moore case): a
  closed dynamics is a step function, a parameterized dynamics is
  `u : (s, a) ↦ u(s, a) ∈ S`;
* the **kernel tangency** `T_s S := List (R × S)` — finite weighted
  mixtures of TARGET POINTS (the house's mixture representation: a
  resolved stochastic step is one honest bundle element, and
  probabilistic mixture is NOT choice); its induced action on an
  observable is the transfer sum, tied below to the landed
  `Qtsl.JumpDiffusion.transferSum`;
* the **powerset tangency** `T_s S := Set S` — built, but presented
  AS AN ENCODING, per the design position (deliberately left open):
  the tangency structure itself is choice-free, and
  a step inclusion arises by CURRYING a parameter axis into the fibre
  (`curryChoice : u ↦ (s ↦ Set.range (u s))`).  At this discrete
  stratum the encoding is lossless and canonical — the fibre itself
  serves as the tautological parameter axis (`curry_tautological`) —
  and the box/diamond faces of the induced action are literally
  quantification over the admitted family (`box_curryChoice`,
  `diamond_curryChoice`), which is the denotation-side story
  (`MdpDemonic` quantifies policies, `StochasticPetriDemonic`
  schedulers).  **The selection seam is named, not crossed**: at the
  analytic stratum the two pictures are equivalent only through
  selection theorems (Filippov/Michael in continuous time, measurable
  selection on the demonic face), whose semicontinuity hypotheses
  belong in those theorems, not in this structure.  Capucci–Myers
  themselves admit `T_s S := 𝒫 S` as a peer primitive; whether the
  choice-free doctrine narrows that remains a deliberately open
  design decision.
-/

namespace SuFunctor

namespace Site

noncomputable section

open CategoryTheory Opposite

universe u

/-- The fibre category over `S`: point-indexed families of types
("bundles over `S`", presented set-theoretically), with pointwise
maps. -/
def Fam (S : Type u) : Type (u + 1) := S → Type u

instance famCategory (S : Type u) : Category.{u} (Fam S) where
  Hom W W' := ∀ s, W s → W' s
  id _ := fun _ x => x
  comp φ ψ := fun s x => ψ s (φ s x)

/-- Reindexing (the cleavage's chosen pullback): precomposition. -/
def famReindex {S T : Type u} (f : T → S) : Fam S ⥤ Fam T where
  obj W := W ∘ f
  map φ := fun t x => φ (f t) x

/-- The indexed category of families, as a strict functor to `Cat`. -/
def famIndexed : (Type u)ᵒᵖ ⥤ Cat.{u, u + 1} where
  obj S := Cat.of (Fam S.unop)
  map f := (famReindex f.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The family cleavage, as a pseudofunctor (identity-iso coherence:
the strict functor promoted along `Functor.toPseudofunctor'`).
`abbrev`, so the strict-plumbing lemmas of `SuFunctor.Site.Tangency`
unify through it. -/
abbrev famCleavage : Pseudofunctor (LocallyDiscrete (Type u)ᵒᵖ) Cat.{u, u + 1} :=
  famIndexed.toPseudofunctor'

/-- The unit parameter bundle (the closed case's `A`). -/
def unitFam (S : Type u) : Fam S := fun _ => PUnit

/-- The family cleavage's unit 2-cell component, at defeq
endpoints. -/
theorem famMapId_app (S : Type u) (W : Fam S) :
    (famCleavage.mapId ⟨op S⟩).inv.toNatTrans.app W = 𝟙 W := by
  rw [strictMapId_inv_app (G := famIndexed) (op S) W rfl]
  rfl

/-- The family cleavage's composition 2-cell component, at defeq
endpoints. -/
theorem famMapComp_app {S S' S'' : Type u} (f : S ⟶ S') (g : S' ⟶ S'')
    (W : Fam S'') :
    (famCleavage.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app W
      = 𝟙 ((famReindex f).obj ((famReindex g).obj W)) := by
  rw [strictMapComp_inv_app (G := famIndexed) g.op f.op W rfl]
  rfl

/-! ## The step tangency (`T_s S = S`) -/

/-- **The step tangency**: each state space's bundle of admissible
changes is the state space itself — one resolved step.  (Capucci–Myers'
basic Moore tangency.) -/
def stepTangency : Tangency (Type u) where
  F := famCleavage
  bundle S := (fun _ => S : Fam S)
  transport f := fun _ x => f x
  transport_id S := by
    rw [famMapId_app]; rfl
  transport_comp f g := by
    rw [famMapComp_app]; rfl

/-- A closed step dynamics is a step function. -/
def stepOfFun {S : Type u} (g : S → S) :
    stepTangency.Dynamics (b := S) (unitFam S) :=
  fun s _ => g s

/-! ## The kernel tangency (`T_s S = List (R × S)`) -/

/-- **The kernel tangency** at weight semiring `R`: admissible changes
are finite weighted mixtures of TARGET POINTS — the house's mixture
representation (resets are point-valued; sub-stochastic deficits are
killing, by the landed Davis convention).  A mixture is one resolved
stochastic step: probabilistic mixture is not choice, and this
tangency is a peer primitive under the choice-free position. -/
def kernelTangency (R : Type u) : Tangency (Type u) where
  F := famCleavage
  bundle S := (fun _ => List (R × S) : Fam S)
  transport f := fun _ l => l.map (Prod.map id f)
  transport_id S := by
    rw [famMapId_app]
    funext s l
    show l.map (Prod.map id id) = l
    simp
  transport_comp f g := by
    rw [famMapComp_app]
    funext s l
    show l.map (Prod.map id fun x => g (f x))
      = (l.map (Prod.map id f)).map (Prod.map id g)
    simp [List.map_map, Prod.map_comp_map, Function.comp_def]

/-- **The induced action of a closed kernel dynamics on an
observable**: the transfer (Koopman/pullback) sum
`(𝒦V)(s) = Σᵢ wᵢ · V(tᵢ)` — integration of the observable against the
finite kernel, exactly the landed transfer shape. -/
def kernelAction {R : Type u} [CommSemiring R] {S : Type u}
    (κ : (kernelTangency R).Dynamics (b := S) (unitFam S)) (V : S → R)
    (s : S) : R :=
  ((κ s PUnit.unit).map fun wt => wt.1 * V wt.2).sum

/-- **The tie to the landed transfer action**: evaluating a mixture of
reset MAPS at a point yields a mixture of target POINTS, and the
kernel tangency's induced action on it is exactly
`Qtsl.JumpDiffusion.transferSum` — the jump-leg integrand of the
landed multi-leg generator. -/
theorem kernelAction_transferSum {n : ℕ}
    (μ : Qtsl.JumpDiffusion.MixtureR n)
    (V : Qtsl.SdeGenerator.State n → ℝ) (z : Qtsl.SdeGenerator.State n) :
    kernelAction (R := ℝ)
      (fun z' _ => μ.map fun wg => (wg.1, wg.2 z')) V z
      = Qtsl.JumpDiffusion.transferSum μ V z := by
  simp [kernelAction, Qtsl.JumpDiffusion.transferSum, List.map_map,
    Function.comp_def]

/-! ## The powerset tangency, as an encoding -/

/-- **The powerset tangency** `T_s S = Set S`.  Under the house
design position this is an ENCODING (a curried choice axis), not a
peer primitive — see the module docstring and `curryChoice`. -/
def powersetTangency : Tangency (Type u) where
  F := famCleavage
  bundle S := (fun _ => Set S : Fam S)
  transport f := fun _ A => f '' A
  transport_id S := by
    rw [famMapId_app]
    funext s A
    show id '' A = A
    simp
  transport_comp f g := by
    rw [famMapComp_app]
    funext s A
    show (fun x => g (f x)) '' A = g '' (f '' A)
    exact (Set.image_image g f A).symm

/-- A step relation, as a closed dynamics over the powerset
tangency. -/
def ofRel {S : Type u} (Φ : S → Set S) :
    powersetTangency.Dynamics (b := S) (unitFam S) :=
  fun s _ => Φ s

/-- The step relation of a closed powerset dynamics. -/
def toRel {S : Type u}
    (κ : powersetTangency.Dynamics (b := S) (unitFam S)) : S → Set S :=
  fun s => κ s PUnit.unit

@[simp] theorem toRel_ofRel {S : Type u} (Φ : S → Set S) :
    toRel (ofRel Φ) = Φ := rfl

/-- **The currying encoding**: a parameterized dynamics over the
CHOICE-FREE step tangency — `u : (s, a) ↦ u(s, a) ∈ S`, one honest
resolved step per parameter value — curries into a closed powerset
dynamics by collecting the range of the parameter axis.  This is the
proposed resolution of the nondeterminism question: the inclusion
picture is the image of the parameterization picture. -/
def curryChoice {S : Type u} {A : Fam S}
    (u : stepTangency.Dynamics (b := S) A) :
    powersetTangency.Dynamics (b := S) (unitFam S) :=
  fun s _ => Set.range (u s)

/-- **Tautological selection, discrete stratum**: every step relation
arises by currying — the fibre itself serves as the parameter axis,
with the evaluation dynamics.  (At the analytic stratum this is where
the selection theorems live, with their semicontinuity hypotheses;
the seam is named in the module docstring and is a ledgered
successor, not crossed here.) -/
theorem curry_tautological {S : Type u} (Φ : S → Set S) :
    curryChoice (A := fun s => (Φ s : Set S))
      (fun s a => (a : S)) = ofRel Φ := by
  funext s p
  show Set.range (fun a : Φ s => (a : S)) = Φ s
  simp [Subtype.range_coe]

/-- The demonic (□) face of the powerset induced action on a
predicate observable. -/
def box {S : Type u} (Φ : S → Set S) (V : S → Prop) : S → Prop :=
  fun s => ∀ t ∈ Φ s, V t

/-- The angelic (◇) face. -/
def diamond {S : Type u} (Φ : S → Set S) (V : S → Prop) : S → Prop :=
  fun s => ∃ t ∈ Φ s, V t

theorem box_mono {S : Type u} (Φ : S → Set S) {V W : S → Prop}
    (h : ∀ t, V t → W t) (s : S) (hb : box Φ V s) : box Φ W s :=
  fun t ht => h t (hb t ht)

theorem diamond_mono {S : Type u} (Φ : S → Set S) {V W : S → Prop}
    (h : ∀ t, V t → W t) (s : S) (hd : diamond Φ V s) : diamond Φ W s :=
  let ⟨t, ht, hv⟩ := hd; ⟨t, ht, h t hv⟩

/-- **The □ face of a curried dynamics is quantification over the
parameter axis** — the denotation-side rendering of demonic choice
(the mechanized face of "denotes by quantification over the admitted
family"). -/
theorem box_curryChoice {S : Type u} {A : Fam S}
    (u : stepTangency.Dynamics (b := S) A) (V : S → Prop) (s : S) :
    box (toRel (curryChoice u)) V s ↔ ∀ a : A s, V (u s a) := by
  simp [box, toRel, curryChoice]

/-- The ◇ face: existential quantification over the parameter axis. -/
theorem diamond_curryChoice {S : Type u} {A : Fam S}
    (u : stepTangency.Dynamics (b := S) A) (V : S → Prop) (s : S) :
    diamond (toRel (curryChoice u)) V s ↔ ∃ a : A s, V (u s a) := by
  simp [diamond, toRel, curryChoice]

end

end Site

end SuFunctor

-- axiom receipts (inline, per the QuantumNet layout)
#print axioms SuFunctor.Site.stepTangency
#print axioms SuFunctor.Site.kernelAction_transferSum
#print axioms SuFunctor.Site.curry_tautological
#print axioms SuFunctor.Site.box_curryChoice
