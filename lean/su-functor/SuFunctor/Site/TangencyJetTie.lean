import SuFunctor.Site.TangencyJet
import QtslAux.SdeGeneratorPoly
import QtslAux.JumpDiffusion

/-! # The induced action of a jet dynamics, and the tie to the landed generator

The rule catalogue's adopted formulation: **the generator is a
tangency-typed dynamics, presented at the certification interface
through its induced action on certificate observables.**  This module
makes that a kernel-checked statement:

* `inducedAction` — the induced action of a closed dynamics over the
  jet tangency on a per-sector polynomial observable: killing
  multiplies, drift pairs the formal gradient, the diffusion columns
  trace the formal Hessian against the derived Gram, and each jump
  leg rides the transfer action at its point-valued reset targets,
  READ AT THE TARGET SECTOR (the cross-sector read is native — no
  displacement picture anywhere).
* `inducedAction_dynOfShaped` — **the tie**: at a single-sector state
  space, the induced action of the dynamics of a polynomial
  presentation IS the landed computed generator
  `Qtsl.SdeGeneratorPoly.genPoly`, every field family live.
* `inducedAction_ofPolyProfile` — coverage: EVERY landed
  `PolyProfile` arises (at its own shape), via the round trip
  `toPolyProfile_ofPolyProfile`.
* `inducedAction_eval` — the semantic corollary through the landed
  hypothesis-free splice (`Qtsl.JumpDiffusion.genPoly_eval_eq_generator`,
  cited not re-proven): the tangency-typed dynamics grounds in the
  semantic integro-differential generator.
* `modeSwitch_fixture` — the two-sector mode-switch: a reset from one
  sector INTO THE OTHER, with the induced action evaluated in closed
  form; the jump term reads the observable's other-sector component
  at the image point.
-/

namespace SuFunctor

namespace Site

noncomputable section

open CategoryTheory MvPolynomial Qtsl.SdeGeneratorPoly

/-! ## Observables and closed jet dynamics -/

/-- Observables on a sectored state space: one polynomial per
sector. -/
def Obs (S : SecState) : Type := ∀ i : S.ι, MvPolynomial (S.κ i) ℚ

/-- The unit parameter bundle over `S`: one sector, no coordinates —
the closed case's `A`. -/
abbrev unitSFib (S : SecState) : SFib S :=
  fun _ => ⟨PUnit, fun _ => Empty, fun _ => inferInstance,
    fun _ => inferInstance⟩

/-- A closed dynamics over the jet tangency at shape `(m, L)`. -/
abbrev JetDyn (m : ℕ) (L : List ℕ) (S : SecState) : Type :=
  (jetTangency m L).Dynamics (b := S) (unitSFib S)

/-- Strip the (empty) fibre variables of a unit-bundle vertical map's
coordinate. -/
def unbase {α : Type} : MvPolynomial (α ⊕ Empty) ℚ →ₐ[ℚ] MvPolynomial α ℚ :=
  rename (Sum.elim id Empty.elim)

@[simp] theorem unbase_rename_inl {α : Type} (p : MvPolynomial α ℚ) :
    unbase (rename Sum.inl p) = p := by
  unfold unbase
  rw [rename_rename]
  rw [show (Sum.elim (id : α → α) Empty.elim ∘ Sum.inl) = id from rfl,
    rename_id, AlgHom.id_apply]

@[simp] theorem unbase_C {α : Type} (a : ℚ) :
    unbase (C a : MvPolynomial (α ⊕ Empty) ℚ) = C a :=
  rename_C _ a

@[simp] theorem unbase_zero {α : Type} :
    unbase (0 : MvPolynomial (α ⊕ Empty) ℚ) = 0 :=
  map_zero _

@[simp] theorem unbase_X_inl {α : Type} (b : α) :
    unbase (X (Sum.inl b) : MvPolynomial (α ⊕ Empty) ℚ) = X b := by
  unfold unbase
  rw [rename_X]
  rfl

open JetCoord in
/-- **The induced action on certificate observables** of a closed jet
dynamics — the rule catalogue's adopted formulation, mechanized.
Mirrors the landed computed generator by construction; the mirror is
`inducedAction_dynOfShaped`. -/
def inducedAction {m : ℕ} {L : List ℕ} {S : SecState}
    (u : JetDyn m L S) (V : Obs S) : Obs S := fun i =>
  let ts := u.sec i PUnit.unit
  let P : JetCoord m L S i ts → MvPolynomial (S.κ i) ℚ :=
    fun c => unbase (u.coord i PUnit.unit c)
  let killT := -(P jKill * V i)
  let driftT := ∑ b, P (jDrift b) * pderiv b (V i)
  let diffT := C (1/2 : ℚ) * ∑ b, ∑ b',
    (∑ k, P (jSigma k b) * P (jSigma k b')) * pderiv b (pderiv b' (V i))
  let jumpT := ∑ j : Fin L.length, P (jRate j) *
    ((∑ t : Fin (L.get j),
        P (jWeight ⟨j, t⟩)
          * bind₁ (fun b => P (jTgt ⟨j, t⟩ b)) (V (ts ⟨j, t⟩)))
      - V i)
  killT + driftT + diffT + jumpT

/-! ## The single-sector face and the tie -/

/-- The single-sector state space on `Fin n` coordinates — the landed
`State n`'s formal face. -/
abbrev singleSec (n : ℕ) : SecState :=
  ⟨PUnit, fun _ => Fin n, fun _ => inferInstance, fun _ => inferInstance⟩

/-- A shape-indexed polynomial presentation — the bundle-shaped form
of the landed `PolyProfile`: rates, weights, and point-valued resets
indexed by the leg shape rather than carried as lists. -/
structure ShapedProfile (n m : ℕ) (L : List ℕ) where
  f : Fin n → MvPolynomial (Fin n) ℚ
  σp : Fin m → Fin n → MvPolynomial (Fin n) ℚ
  kill : MvPolynomial (Fin n) ℚ
  rate : Fin L.length → MvPolynomial (Fin n) ℚ
  weight : ∀ j : Fin L.length, Fin (L.get j) → ℚ
  reset : ∀ j : Fin L.length, Fin (L.get j) → Fin n → MvPolynomial (Fin n) ℚ

/-- The landed list-shaped presentation of a shaped profile. -/
def ShapedProfile.toPolyProfile {n m : ℕ} {L : List ℕ}
    (Q : ShapedProfile n m L) : PolyProfile n m where
  f := Q.f
  σp := Q.σp
  kill := Q.kill
  legs := List.ofFn fun j =>
    (Q.rate j, List.ofFn fun t => (Q.weight j t, Q.reset j t))

open JetCoord in
/-- The closed jet dynamics of a shaped presentation: drift/σ/kill/
rate slots carry the presentation's polynomials, weight slots its
constants, reset-target slots its (point-valued) reset coordinates;
all targets stay in the single sector. -/
def dynOfShaped {n m : ℕ} {L : List ℕ} (Q : ShapedProfile n m L) :
    JetDyn m L (singleSec n) where
  sec _ _ := fun _ => PUnit.unit
  coord _ _ c :=
    match c with
    | Sum.inl b => rename Sum.inl (Q.f b)
    | Sum.inr (Sum.inl (k, b)) => rename Sum.inl (Q.σp k b)
    | Sum.inr (Sum.inr (Sum.inl _)) => rename Sum.inl Q.kill
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl j))) => rename Sum.inl (Q.rate j)
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))) =>
        C (Q.weight t.1 t.2)
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨t, b⟩)))) =>
        rename Sum.inl (Q.reset t.1 t.2 b)

/-- Embed a single-sector observable. -/
def obsOf {n : ℕ} (V : MvPolynomial (Fin n) ℚ) : Obs (singleSec n) :=
  fun _ => V

/-- `(List.ofFn g).sum`, Fin-indexed. -/
private theorem sum_ofFn' {M : Type} [AddCommMonoid M] :
    ∀ {k : ℕ} (F : Fin k → M), (List.ofFn F).sum = ∑ j, F j
  | 0, F => by simp
  | (k + 1), F => by
      rw [List.ofFn_succ, List.sum_cons, sum_ofFn' (fun j => F j.succ),
        Fin.sum_univ_succ]

/-- Mapped-`ofFn` sums are Fin-indexed sums. -/
private theorem sum_map_ofFn {α : Type*} {M : Type} [AddCommMonoid M]
    {k : ℕ} (g : Fin k → α) (h : α → M) :
    ((List.ofFn g).map h).sum = ∑ j, h (g j) := by
  rw [List.map_ofFn]
  exact sum_ofFn' _

/-- **THE TIE**: the induced action of the jet-tangency dynamics of a
polynomial presentation IS the landed computed generator — killing
multiplies, drift pairs the formal gradient, diffusion traces the
formal Hessian against the derived Gram, jumps ride the transfer at
point-valued resets — for every field family, at every observable.
(The rule catalogue's adopted formulation, as a kernel-checked
equation.) -/
theorem inducedAction_dynOfShaped {n m : ℕ} {L : List ℕ}
    (Q : ShapedProfile n m L) (V : MvPolynomial (Fin n) ℚ) (i : PUnit) :
    inducedAction (dynOfShaped Q) (obsOf V) i
      = genPoly Q.toPolyProfile V := by
  have hmix : ∀ j : Fin L.length,
      transferMix (List.ofFn fun t => (Q.weight j t, Q.reset j t)) V
        = ∑ t : Fin (L.get j), C (Q.weight j t) * bind₁ (Q.reset j t) V := by
    intro j
    unfold transferMix
    exact sum_map_ofFn _ _
  have hleg : ((Q.toPolyProfile.legs.map fun lm =>
      lm.1 * (transferMix lm.2 V - V)).sum : MvPolynomial (Fin n) ℚ)
      = ∑ j : Fin L.length, Q.rate j *
          ((∑ t : Fin (L.get j), C (Q.weight j t) * bind₁ (Q.reset j t) V)
            - V) := by
    show ((List.ofFn _).map _).sum = _
    rw [sum_map_ofFn]
    exact Finset.sum_congr rfl fun j _ => by rw [hmix j]
  calc inducedAction (dynOfShaped Q) (obsOf V) i
      = -(Q.kill * V) + (∑ b, Q.f b * pderiv b V)
          + C (1/2 : ℚ) * ∑ b, ∑ b',
              (∑ k, Q.σp k b * Q.σp k b') * pderiv b (pderiv b' V)
          + ∑ j : Fin L.length, Q.rate j *
              ((∑ t : Fin (L.get j),
                  C (Q.weight j t) * bind₁ (Q.reset j t) V) - V) := by
        simp only [inducedAction, dynOfShaped, obsOf, unitSFib, singleSec,
          unbase_rename_inl, unbase_C]
      _ = genPoly Q.toPolyProfile V := by
        unfold genPoly PolyProfile.gram
        rw [hleg]
        rfl

/-! ## Coverage: every landed presentation arises -/

/-- The leg shape of a landed presentation. -/
def shapeOf {n : ℕ} (legs : List (MvPolynomial (Fin n) ℚ × Mixture n ℚ)) :
    List ℕ :=
  legs.map fun lm => lm.2.length

theorem shapeOf_length {n : ℕ}
    (legs : List (MvPolynomial (Fin n) ℚ × Mixture n ℚ)) :
    (shapeOf legs).length = legs.length :=
  List.length_map ..

theorem shapeOf_get {n : ℕ}
    (legs : List (MvPolynomial (Fin n) ℚ × Mixture n ℚ))
    (j : Fin (shapeOf legs).length) :
    (shapeOf legs).get j
      = (legs.get (Fin.cast (shapeOf_length legs) j)).2.length := by
  simp [shapeOf, List.get_eq_getElem, List.getElem_map]

/-- The shaped form of a landed presentation, at its own shape. -/
def ofPolyProfile {n m : ℕ} (P : PolyProfile n m) :
    ShapedProfile n m (shapeOf P.legs) where
  f := P.f
  σp := P.σp
  kill := P.kill
  rate j := (P.legs.get (Fin.cast (shapeOf_length P.legs) j)).1
  weight j t := ((P.legs.get (Fin.cast (shapeOf_length P.legs) j)).2.get
    (Fin.cast (shapeOf_get P.legs j) t)).1
  reset j t := ((P.legs.get (Fin.cast (shapeOf_length P.legs) j)).2.get
    (Fin.cast (shapeOf_get P.legs j) t)).2

/-- The round trip: shaping then listing is the identity — the
coverage lemma. -/
theorem toPolyProfile_ofPolyProfile {n m : ℕ} (P : PolyProfile n m) :
    (ofPolyProfile P).toPolyProfile = P := by
  obtain ⟨f, σp, kill, legs⟩ := P
  simp only [ofPolyProfile, ShapedProfile.toPolyProfile]
  congr 1
  apply List.ext_getElem
  · simp [shapeOf_length]
  · intro k h1 h2
    simp only [List.getElem_ofFn, List.get_eq_getElem, Fin.coe_cast]
    refine Prod.ext rfl ?_
    apply List.ext_getElem
    · simp [shapeOf]
    · intro t h3 h4
      simp only [List.getElem_ofFn, List.get_eq_getElem, Fin.val_cast]
      rfl

/-- **Coverage corollary**: for EVERY landed polynomial presentation,
the induced action of its jet-tangency dynamics is the landed
computed generator. -/
theorem inducedAction_ofPolyProfile {n m : ℕ} (P : PolyProfile n m)
    (V : MvPolynomial (Fin n) ℚ) (i : PUnit) :
    inducedAction (dynOfShaped (ofPolyProfile P)) (obsOf V) i
      = genPoly P V := by
  rw [inducedAction_dynOfShaped, toPolyProfile_ofPolyProfile]

/-- **The semantic corollary, through the landed hypothesis-free
splice**: evaluating the induced action of a jet-tangency dynamics
equals the semantic integro-differential generator at the formal
derivative data — the tangency grounds in
`Qtsl.JumpDiffusion.generator` with zero re-proof. -/
theorem inducedAction_eval {n m : ℕ} {L : List ℕ} (Q : ShapedProfile n m L)
    (V : MvPolynomial (Fin n) ℚ) (z : Qtsl.SdeGenerator.State n) :
    (aeval z (inducedAction (dynOfShaped Q) (obsOf V) PUnit.unit) : ℝ)
      = Qtsl.JumpDiffusion.generator Q.toPolyProfile.toJd
          (fun w => (aeval w V : ℝ))
          (fun w b => (aeval w (pderiv b V) : ℝ))
          (fun w b b' => (aeval w (pderiv b (pderiv b' V)) : ℝ)) z := by
  rw [inducedAction_dynOfShaped]
  exact Qtsl.JumpDiffusion.genPoly_eval_eq_generator Q.toPolyProfile V z

/-! ## The two-sector mode-switch fixture -/

/-- Two one-dimensional sectors. -/
abbrev twoSec : SecState :=
  ⟨Bool, fun _ => Fin 1, fun _ => inferInstance, fun _ => inferInstance⟩

open JetCoord in
/-- **The mode-switch dynamics** (shape: no diffusion, one Dirac
leg): from each sector, unit drift, zero killing, and a unit-rate
jump whose reset TARGETS THE OTHER SECTOR, carrying the coordinate
over — the cross-sector reset no displacement picture can express. -/
def modeSwitch : JetDyn 0 [1] twoSec where
  sec i _ := fun _ => !i
  coord _ _ c :=
    match c with
    | Sum.inl _ => C 1
    | Sum.inr (Sum.inl (k, _)) => Fin.elim0 k
    | Sum.inr (Sum.inr (Sum.inl _)) => 0
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => C 1
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) => C 1
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨_, b⟩)))) =>
        X (Sum.inl b)

/-- A per-sector observable with genuinely different polynomials per
sector: `x` on the `false` sector, `x²` on the `true` sector. -/
def vObs : Obs twoSec := fun i =>
  cond i (X (0 : Fin 1) ^ 2) (X (0 : Fin 1))

/-- **The fixture, in closed form**: at the `false` sector the
induced action reads the observable's `true`-sector component through
the cross-sector reset —
`𝒜V = 1·∂ₓ(x) + 1·(V_true(x) − V_false(x)) = 1 + (x² − x)`.
(This is the equation mutant M2 kills: reading `V` at the source
instead of the reset target cannot even typecheck across sectors.) -/
theorem modeSwitch_fixture :
    inducedAction modeSwitch vObs false
      = C 1 + (X (0 : Fin 1) ^ 2 - X (0 : Fin 1)) := by
  simp only [inducedAction, modeSwitch, vObs, twoSec, unitSFib,
    unbase_C, unbase_zero, unbase_X_inl]
  simp [Fin.sum_univ_one, List.get, pderiv_X_self, bind₁_X_left]

end

end Site

end SuFunctor

-- axiom receipts (inline, per the QuantumNet layout)
#print axioms SuFunctor.Site.jetTangency
#print axioms SuFunctor.Site.pderiv_bind₁
#print axioms SuFunctor.Site.inducedAction_dynOfShaped
#print axioms SuFunctor.Site.inducedAction_ofPolyProfile
#print axioms SuFunctor.Site.inducedAction_eval
#print axioms SuFunctor.Site.modeSwitch_fixture
