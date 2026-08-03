import SuFunctor.HypernetInclusion
import Qtsl.PpolyExpansion

/-! # Views elaborate in: the θ-image of a packaged view is its elaboration's

The single-genus rule: hypernets are the one genus of computational
content, and every other surface syntax — packaged polynomial views,
ReLU, jet-polynomial content — is a *view*: an admissible packaged
symbol with a definitional expansion into core primitives.  This module
mechanizes the semantic half of that rule against the mechanized
semantic universe: **a view is semantically nothing over and above its
elaboration**.

A view symbol and its expansion hypernet live over different apexes —
the expansion has internal wires — so the statement is a
*marginalization*, not a bare `austereDnf` equality: the view's
admissible region is the **image** of the expansion's under boundary
restriction, and θ of the view is the **direct image** (min-plus
pushforward) of θ of the expansion along that restriction.

## Main statements

* `Plain.Pen.push` / `Plain.Pen.push_possWall` — the direct image of a
  penalty along a carrier map, exact on possibilistic walls: the
  pushforward of the wall of a region is the wall of the image.  The
  scalar content of elaboration correctness.
* `restrictCell` — for nested apexes with shared feet, the identity map
  is an `AlignedCell`; `renameTot` at it is boundary restriction.
* `dnfPush` — DNF-level covariant transport (atom-wise direct image);
  the properness mark is a fixed point, so option-A shape is preserved.
* `theta_elab` — the schema: an elaboration whose admissible region
  projects onto the view's has the view's θ-image as the direct image
  of its own.
* `theta_elab_ppoly` — the witness at the canonical packaged-polynomial
  instance: the view's admissible region *is* the boundary projection
  of `ppolyExpH`'s (`ppoly_admRegion_projection`), hence
  θ(elaboration), marginalized to the boundary, *is* θ(view).

## Descent anchor

The summit is `SuFunctor.Spacetime.SemanticUniverse`
(module `SuFunctor.Spacetime.Universe`);
its spec storey has the landed `dnfSpecFunctor` fibres definitionally
(`spacetimeSpecFunctor_fibre_eq`), and per-site conservativity places
the one-site `WireSpan` world inside the profiled base at constant
profiles.  θ (`SuFunctor.HypernetInclusion`) lands in those fibres;
this module's statements are in θ's codomain vocabulary.
-/

namespace SuFunctor

noncomputable section

open CategoryTheory CategoryTheory.WireSpan PPLC
open SuFunctor.Plain SuFunctor.Universe
open scoped NNReal ENNReal

/-! ## The direct image of a penalty

The covariant transport: a penalty pushes forward along a carrier map
by infimum over the joint-pushforward fibre — the min-plus direct
image.  On possibilistic walls it is exact: walls take only the values
`0` and `⊤`, and the infimum is either witnessed at `0` or ranges over
`⊤`. -/

namespace Plain

universe u

variable {X Y : Type u}

/-- The direct image of a penalty along a carrier map: infimum over
the pushforward fibre. -/
def Pen.push (h : X → Y) (f : Pen X) : Pen Y :=
  fun ν => ⨅ (μ : Joint X) (_ : μ.push h = ν), f μ

/-- Credal sets are monotone in the region. -/
theorem suppIn_mono {B C : Set X} (hBC : B ⊆ C) : suppIn B ⊆ suppIn C :=
  fun _ hμ => hμ.trans hBC

/-- Every joint supported in the image of a region is the pushforward
of a joint supported in the region: push along a section of `g` chosen
on the support.  Mass rides the pushforward, so no normalization is
lost. -/
theorem Joint.exists_push_section {g : X → Y} {B : Set X} {ν : Joint Y}
    (hν : ν ∈ suppIn (g '' B)) : ∃ μ ∈ suppIn B, μ.push g = ν := by
  classical
  by_cases h0 : ν.wt = 0
  · refine ⟨Joint.zero X, fun x hx => ?_, ?_⟩
    · rw [Joint.zero_wt] at hx
      simp at hx
    · refine Joint.ext ?_
      rw [Joint.push_wt, Joint.zero_wt, Finsupp.mapDomain_zero, h0]
  · obtain ⟨y₀, hy₀⟩ := Finsupp.support_nonempty_iff.mpr h0
    have hy₀B : y₀ ∈ g '' B := hν (Finset.mem_coe.mpr hy₀)
    let s : Y → X := fun y =>
      if hy : y ∈ g '' B then hy.choose else hy₀B.choose
    have hs_mem : ∀ y ∈ g '' B, s y ∈ B := by
      intro y hy
      simp only [s, dif_pos hy]
      exact hy.choose_spec.1
    have hs_sec : ∀ y ∈ g '' B, g (s y) = y := by
      intro y hy
      simp only [s, dif_pos hy]
      exact hy.choose_spec.2
    refine ⟨ν.push s, ?_, ?_⟩
    · intro x hx
      have hx' : x ∈ (ν.wt.mapDomain s).support := by simpa using hx
      obtain ⟨v, hv, rfl⟩ :=
        Finset.mem_image.mp (Finsupp.mapDomain_support hx')
      exact hs_mem v (hν (Finset.mem_coe.mpr hv))
    · rw [Joint.push_push]
      refine Joint.ext ?_
      rw [Joint.push_wt]
      exact (Finsupp.mapDomain_congr
        (g := id)
        (fun y hy => hs_sec y (hν (Finset.mem_coe.mpr hy)))).trans
        Finsupp.mapDomain_id

/-- **The direct image of a wall is the wall of the image** — exactly.
The elaboration-correctness scalar law: marginalizing a possibilistic
coupling projects its region. -/
theorem Pen.push_possWall (g : X → Y) (B : Set X) :
    Pen.push g (possWall B) = possWall (g '' B) := by
  funext ν
  by_cases hν : ν ∈ suppIn (g '' B)
  · obtain ⟨μ, hμB, hμν⟩ := Joint.exists_push_section hν
    rw [possWall_apply_of_mem hν]
    refine le_antisymm ?_ zero_le
    exact (iInf₂_le μ hμν).trans_eq (possWall_apply_of_mem hμB)
  · rw [possWall_apply_of_notMem hν]
    refine iInf_eq_top.mpr fun μ => iInf_eq_top.mpr fun hμ => ?_
    refine possWall_apply_of_notMem fun hc => hν ?_
    rw [← hμ]
    exact suppIn_push.mpr
      (suppIn_mono (Set.subset_preimage_image g B) hc)

/-- The top penalty is a fixed point of the direct image: every fibre
infimum of `⊤` is `⊤`. -/
theorem Pen.push_top (g : X → Y) :
    Pen.push g (⊤ : Pen X) = (⊤ : Pen Y) := by
  funext ν
  exact iInf_eq_top.mpr fun μ => iInf_eq_top.mpr fun _ => rfl

/-- The properness-mark singleton is a fixed point of the direct
image. -/
theorem push_top_singleton (g : X → Y) :
    Pen.push g '' ({⊤} : Set (Pen X)) = {⊤} := by
  rw [Set.image_singleton, Pen.push_top]

end Plain

/-! ## Boundary restriction and the DNF-level direct image -/

variable (ty : Wire → Option TensorType)

variable {X Y : Finset Wire}

/-- For nested apexes with shared feet, the identity map is a renaming
cell: `renameTot` at it is boundary restriction of apex states. -/
def restrictCell {m₁ m₂ : AlignedLoose X Y} (hsub : m₁.apex ⊆ m₂.apex) :
    AlignedCell ty m₁ m₂ where
  map := id
  mem := fun _ hw => hsub hw
  ty_eq := fun _ _ => rfl
  left_mem := fun _ hw => hw
  right_mem := fun _ hw => hw

universe u

/-- Atom-level direct image: floor and marks push forward; the
properness mark is a fixed point, so option-A shape is preserved by
construction. -/
def atomPush {A B : Type u} (g : A → B)
    (a : SpecAtom (Plain.Joint A)) : SpecAtom (Plain.Joint B) where
  floor := Plain.Pen.push g a.floor
  marks := Plain.Pen.push g '' a.marks
  finite_marks := a.finite_marks.image _
  top_mem := ⟨⊤, a.top_mem, Plain.Pen.push_top g⟩

/-- DNF-level direct image: atom transport, disjunct-wise. -/
def dnfPush {A B : Type u} (g : A → B)
    (D : SpecDnf (Plain.Joint A)) : SpecDnf (Plain.Joint B) :=
  ⟨atomPush g '' D.atoms, D.finite_atoms.image _⟩

/-! ## The elaboration law, generically

A view (a diagram over the boundary apex) and an elaboration (a diagram
over an enlarged apex, same feet) with the *shared-region* property —
the view's admissible region is the image of the elaboration's under
boundary restriction — have the same θ-image up to marginalization:
θ of the view IS the direct image of θ of the elaboration. -/

/-- **The elaboration law**: a view is semantically nothing over and
above its elaboration.  The floor computation is `Pen.push_possWall`
at the shared region; the properness mark transports to itself. -/
theorem theta_elab {m₁ m₂ : AlignedLoose X Y} (hsub : m₁.apex ⊆ m₂.apex)
    (T₁ T₂ : List PrimApp)
    (hregion : AdmRegion ty m₁ T₁
      = renameTot ty (restrictCell ty hsub) '' AdmRegion ty m₂ T₂) :
    dnfPush (renameTot ty (restrictCell ty hsub)) (austereDnf ty m₂ T₂)
      = austereDnf ty m₁ T₁ := by
  refine SpecDnf.ext ?_
  show atomPush (renameTot ty (restrictCell ty hsub))
      '' {austereAtom ty m₂ T₂} = {austereAtom ty m₁ T₁}
  rw [Set.image_singleton]
  refine congrArg _ (SpecAtom.ext ?_ ?_)
  · show Plain.Pen.push (renameTot ty (restrictCell ty hsub))
        (possWall (AdmRegion ty m₂ T₂))
      = possWall (AdmRegion ty m₁ T₁)
    rw [Plain.Pen.push_possWall, ← hregion]
  · show Plain.Pen.push (renameTot ty (restrictCell ty hsub))
        '' (austereAtom ty m₂ T₂).marks
      = ({⊤} : Set (Pen (Pat.Tot (alignedPat ty m₁))))
    rw [show (austereAtom ty m₂ T₂).marks = {⊤} from rfl]
    exact Plain.push_top_singleton _

/-! ## The packaged-polynomial witness

The canonical `ppoly` instance (`PPLC.PpolyExpansion`): view apex
`{0, 6}`, expansion apex `{0, …, 6}`, feet `{0}` and `{6}`, ambient
table `expTy`.  The Catalogue-level pair `ppoly_semOk_canon_iff` /
`ppoly_expansion_sound`/`_complete` lifts to the shared-region
property, and the elaboration law instantiates. -/

namespace PpolyElab

open PPLC.PpolyExpansion

/-- The view's apex: the packaged symbol's own wires. -/
def viewApex : Finset Wire := {0, 6}

/-- The elaboration's apex: boundary plus internal wires. -/
def expApex : Finset Wire := {0, 1, 2, 3, 4, 5, 6}

/-- The input foot. -/
def inFeet : Finset Wire := {0}

/-- The output foot. -/
def outFeet : Finset Wire := {6}

/-- The view as an aligned loose arrow. -/
def mView : AlignedLoose inFeet outFeet :=
  ⟨viewApex, by decide, by decide⟩

/-- The elaboration as an aligned loose arrow. -/
def mExp : AlignedLoose inFeet outFeet :=
  ⟨expApex, by decide, by decide⟩

theorem hsubVE : mView.apex ⊆ mExp.apex := by decide

/-- The packaged view symbol at the canonical instance. -/
def ppolyApp : PrimApp := .ppoly 1 qCanon [0] 6

theorem expTy0 : expTy 0 = some ⟨[], Dtype.Q⟩ := rfl

theorem expTy6 : expTy 6 = some ⟨[], Dtype.Q⟩ := rfl

theorem mem_viewApex_0 : (0 : Wire) ∈ viewApex := by decide

theorem mem_viewApex_6 : (6 : Wire) ∈ viewApex := by decide

theorem mem_expApex_0 : (0 : Wire) ∈ expApex := by decide

theorem mem_expApex_6 : (6 : Wire) ∈ expApex := by decide

/-- The ambient table restricted to the expansion apex is the
expansion's own table: `expTy` types exactly the wires `0`–`6`. -/
theorem tableOn_expTy : ∀ w, tableOn expTy expApex w = expTy w := by
  intro w
  by_cases hw : w ∈ expApex
  · exact tableOn_pos expTy hw
  · rw [tableOn_neg expTy hw]
    simp only [expApex, Finset.mem_insert, Finset.mem_singleton,
      not_or] at hw
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hw
    simp [expTy, h0, h1, h2, h3, h4, h5, h6]

/-- Type-exactness of the identity between the aligned stratum's table
and the expansion hypernet's. -/
theorem htyE : ∀ w,
    (vacNet (tableOn expTy expApex)).wireType (id w)
      = ppolyExpH.wireType w :=
  fun w => tableOn_expTy w

/-- The reverse direction. -/
theorem htyE' : ∀ w,
    ppolyExpH.wireType (id w)
      = (vacNet (tableOn expTy expApex)).wireType w :=
  fun w => (tableOn_expTy w).symm

/-- The aligned stratum's table types an apex wire as the ambient
table does. -/
theorem vacTy {W : Finset Wire} {w : Wire} (hw : w ∈ W)
    {τ : TensorType} (hty : expTy w = some τ) :
    (vacNet (tableOn expTy W)).wireType w = some τ := by
  show tableOn expTy W w = some τ
  rw [tableOn_pos expTy hw]
  exact hty

/-- Admissibility over the expansion loose is admissibility of the
transported `ppolyExpH` valuation: the fourteen-case transport at the
identity rename. -/
theorem mem_admRegion_exp_iff (t : Pat.Tot (alignedPat expTy mExp)) :
    t ∈ AdmRegion expTy mExp ppolyExpH.applications
      ↔ ((toValuation expTy t.2.2.2.1).pull id htyE).Admissible := by
  show (∀ a ∈ ppolyExpH.applications,
      a.SemOk (toValuation expTy t.2.2.2.1))
    ↔ ∀ a ∈ ppolyExpH.applications,
      a.SemOk ((toValuation expTy t.2.2.2.1).pull id htyE)
  refine forall₂_congr fun a ha => ?_
  have h := PrimApp.SemOk_rename id htyE (toValuation expTy t.2.2.2.1) a
    (ppolyExpH.typeConsistent a ha)
  rw [PrimApp.rename_id] at h
  exact h

/-- Membership in the view's region reads through the canonical
`ppoly` semantics. -/
theorem mem_admRegion_view_iff (t : Pat.Tot (alignedPat expTy mView)) :
    t ∈ AdmRegion expTy mView [ppolyApp]
      ↔ ∃ p y : ℚ,
        (toValuation expTy t.2.2.2.1).entryFlat 0 0 = some (.fin p) ∧
        (toValuation expTy t.2.2.2.1).entryFlat 6 0 = some (.fin y) ∧
        y = MonoTable.evalQ qCanon [p] := by
  show (∀ a ∈ [ppolyApp], a.SemOk (toValuation expTy t.2.2.2.1)) ↔ _
  constructor
  · intro h
    exact (ppoly_semOk_canon_iff (toValuation expTy t.2.2.2.1)).mp
      (h _ (List.mem_singleton.mpr rfl))
  · intro h a ha
    rw [List.mem_singleton] at ha
    subst ha
    exact (ppoly_semOk_canon_iff (toValuation expTy t.2.2.2.1)).mpr h

/-- A rational-scalar tensor value always reads a finite rational: the
`Q` carrier excludes infinities. -/
theorem qscalar_entryE_fin (v : TensorValue ⟨[], Dtype.Q⟩) :
    ∃ p : ℚ, v.entryE 0 = some (.fin p) := by
  obtain ⟨l, hl⟩ := v
  have hl1 : l.length = 1 := hl
  rcases l with _ | ⟨c, l⟩
  · simp at hl1
  rcases l with _ | ⟨c₂, l⟩
  · obtain ⟨e, he⟩ := c
    cases e with
    | fin q => exact ⟨q, rfl⟩
    | negInf => exact nomatch he.1
    | posInf => exact nomatch he
  · simp at hl1

/-- Scalar determination: a rational-scalar tensor value is determined
by its single entry. -/
theorem qscalar_ext {v v' : TensorValue ⟨[], Dtype.Q⟩}
    (h : v.entryE 0 = v'.entryE 0) : v = v' := by
  obtain ⟨l, hl⟩ := v
  obtain ⟨l', hl'⟩ := v'
  have hl1 : l.length = 1 := hl
  have hl1' : l'.length = 1 := hl'
  rcases l with _ | ⟨c, l⟩
  · simp at hl1
  rcases l with _ | ⟨c₂, l⟩
  · rcases l' with _ | ⟨c', l'⟩
    · simp at hl1'
    rcases l' with _ | ⟨c₂', l'⟩
    · have hcc : c.val = c'.val :=
        Option.some.inj (show some c.val = some c'.val from h)
      apply Subtype.ext
      show [c] = [c']
      rw [Subtype.ext hcc]
    · simp at hl1'
  · simp at hl1

/-- Two aligned valuations read the same entries at a wire whose
stored values agree. -/
theorem toValuation_entryFlat_congr {W₁ W₂ : Finset Wire}
    {s₁ : states (ctxIface W₁)} {s₂ : states (ctxIface W₂)}
    {hs₁ : Conformant expTy W₁ s₁} {hs₂ : Conformant expTy W₂ s₂}
    {w : Wire} (hw₁ : w ∈ W₁) (hw₂ : w ∈ W₂) {τ : TensorType}
    (hty : expTy w = some τ)
    (hval : s₁ ⟨w, hw₁⟩ = s₂ ⟨w, hw₂⟩) (i : ℕ) :
    (toValuation expTy hs₁).entryFlat w i
      = (toValuation expTy hs₂).entryFlat w i := by
  rw [Hypernet.Valuation.entryFlat_some
      (toValuation expTy hs₁) (vacTy hw₁ hty) i,
    Hypernet.Valuation.entryFlat_some
      (toValuation expTy hs₂) (vacTy hw₂ hty) i]
  exact congrArg (fun v : TensorValue τ => v.entryE i)
    (ElVal.valueOf_congr hval _ _)

/-- Boundary restriction preserves reads: the restricted point's
valuation reads the stored value of the full point. -/
theorem restrict_entryFlat (te : Pat.Tot (alignedPat expTy mExp))
    {w : Wire} (hw : w ∈ viewApex) {τ : TensorType}
    (hty : expTy w = some τ) (i : ℕ) :
    (toValuation expTy
        (renameTot expTy (restrictCell expTy hsubVE)
          te).2.2.2.1).entryFlat w i
      = (toValuation expTy te.2.2.2.1).entryFlat w i :=
  toValuation_entryFlat_congr hw (hsubVE hw) hty rfl i

/-! ### The mixed state

The `⊆` inclusion's construction: an expansion point carrying the view
point's own values on the boundary and the completeness witness's
values on the internal wires. -/

/-- The mixed state over the expansion apex. -/
def mixState (t : Pat.Tot (alignedPat expTy mView))
    (σ : ppolyExpH.Valuation) : states (ctxIface expApex) :=
  fun w =>
    if h : w.1 ∈ viewApex then t.2.2.1 ⟨w.1, h⟩
    else stateOfValuation expTy (σ.pull id htyE') ⟨w.1, w.2⟩

theorem mixState_pos (t : Pat.Tot (alignedPat expTy mView))
    (σ : ppolyExpH.Valuation) {w : Wire} (hwE : w ∈ expApex)
    (hv : w ∈ viewApex) :
    mixState t σ ⟨w, hwE⟩ = t.2.2.1 ⟨w, hv⟩ := by
  unfold mixState
  exact dif_pos hv

theorem mixState_neg (t : Pat.Tot (alignedPat expTy mView))
    (σ : ppolyExpH.Valuation) {w : Wire} (hwE : w ∈ expApex)
    (hv : w ∉ viewApex) :
    mixState t σ ⟨w, hwE⟩
      = stateOfValuation expTy (σ.pull id htyE') ⟨w, hwE⟩ := by
  unfold mixState
  exact dif_neg hv

theorem mixState_conformant (t : Pat.Tot (alignedPat expTy mView))
    (σ : ppolyExpH.Valuation) :
    Conformant expTy expApex (mixState t σ) := by
  intro w
  show (mixState t σ w).map Sigma.fst = expTy w.1
  unfold mixState
  by_cases h : w.1 ∈ viewApex
  · rw [dif_pos h]
    exact t.2.2.2.1 ⟨w.1, h⟩
  · rw [dif_neg h]
    exact stateOfValuation_conformant expTy (σ.pull id htyE') ⟨w.1, w.2⟩

theorem mixState_left (t : Pat.Tot (alignedPat expTy mView))
    (σ : ppolyExpH.Valuation) :
    ∀ w : {w : Wire // w ∈ inFeet},
      mixState t σ ⟨w.1, mExp.left_le w.2⟩ = t.1 w := by
  intro w
  have h : w.1 ∈ viewApex := mView.left_le w.2
  rw [mixState_pos t σ (mExp.left_le w.2) h]
  exact t.2.2.2.2.1 w

theorem mixState_right (t : Pat.Tot (alignedPat expTy mView))
    (σ : ppolyExpH.Valuation) :
    ∀ w : {w : Wire // w ∈ outFeet},
      mixState t σ ⟨w.1, mExp.right_le w.2⟩ = t.2.1 w := by
  intro w
  have h : w.1 ∈ viewApex := mView.right_le w.2
  rw [mixState_pos t σ (mExp.right_le w.2) h]
  exact t.2.2.2.2.2 w

/-- The mixed state's boundary reads are the view point's. -/
theorem mixState_read0 (t : Pat.Tot (alignedPat expTy mView))
    (σ : ppolyExpH.Valuation) :
    (toValuation expTy (mixState_conformant t σ)).entryFlat 0 0
      = (toValuation expTy t.2.2.2.1).entryFlat 0 0 :=
  toValuation_entryFlat_congr mem_expApex_0 mem_viewApex_0 expTy0
    (mixState_pos t σ mem_expApex_0 mem_viewApex_0) 0

theorem mixState_read6 (t : Pat.Tot (alignedPat expTy mView))
    (σ : ppolyExpH.Valuation) :
    (toValuation expTy (mixState_conformant t σ)).entryFlat 6 0
      = (toValuation expTy t.2.2.2.1).entryFlat 6 0 :=
  toValuation_entryFlat_congr mem_expApex_6 mem_viewApex_6 expTy6
    (mixState_pos t σ mem_expApex_6 mem_viewApex_6) 0

/-- **The mixed state's valuation is the completeness witness**: on
internal wires by construction, on the boundary by scalar
determination against the shared reads. -/
theorem mixState_pull_eq (t : Pat.Tot (alignedPat expTy mView))
    (σ : ppolyExpH.Valuation)
    (hσ0 : σ.entryFlat 0 0 = (toValuation expTy t.2.2.2.1).entryFlat 0 0)
    (hσ6 : σ.entryFlat 6 0 = (toValuation expTy t.2.2.2.1).entryFlat 6 0) :
    (toValuation expTy (mixState_conformant t σ)).pull id htyE = σ := by
  funext w τ h
  show toValuation expTy (mixState_conformant t σ) w τ ((htyE w).trans h)
    = σ w τ h
  by_cases hv : w ∈ viewApex
  · have hw06 : w = 0 ∨ w = 6 := by
      simpa [viewApex, Finset.mem_insert, Finset.mem_singleton] using hv
    rcases hw06 with rfl | rfl
    · have hτ : τ = ⟨[], Dtype.Q⟩ := by
        have h' : some (⟨[], Dtype.Q⟩ : TensorType) = some τ := h
        exact (Option.some.inj h').symm
      subst hτ
      refine qscalar_ext ?_
      calc (toValuation expTy (mixState_conformant t σ) 0 ⟨[], Dtype.Q⟩
              ((htyE 0).trans h)).entryE 0
          = (toValuation expTy (mixState_conformant t σ)).entryFlat 0 0 :=
            (Hypernet.Valuation.entryFlat_some _ ((htyE 0).trans h) 0).symm
        _ = (toValuation expTy t.2.2.2.1).entryFlat 0 0 :=
            mixState_read0 t σ
        _ = σ.entryFlat 0 0 := hσ0.symm
        _ = (σ 0 ⟨[], Dtype.Q⟩ h).entryE 0 :=
            Hypernet.Valuation.entryFlat_some σ h 0
    · have hτ : τ = ⟨[], Dtype.Q⟩ := by
        have h' : some (⟨[], Dtype.Q⟩ : TensorType) = some τ := h
        exact (Option.some.inj h').symm
      subst hτ
      refine qscalar_ext ?_
      calc (toValuation expTy (mixState_conformant t σ) 6 ⟨[], Dtype.Q⟩
              ((htyE 6).trans h)).entryE 0
          = (toValuation expTy (mixState_conformant t σ)).entryFlat 6 0 :=
            (Hypernet.Valuation.entryFlat_some _ ((htyE 6).trans h) 0).symm
        _ = (toValuation expTy t.2.2.2.1).entryFlat 6 0 :=
            mixState_read6 t σ
        _ = σ.entryFlat 6 0 := hσ6.symm
        _ = (σ 6 ⟨[], Dtype.Q⟩ h).entryE 0 :=
            Hypernet.Valuation.entryFlat_some σ h 0
  · have hwE : w ∈ expApex := by
      have h' : tableOn expTy expApex w = some τ := (htyE w).trans h
      exact mem_of_tableOn_some expTy h'
    have hty : expTy w = some τ := h
    have hstate : mixState t σ ⟨w, hwE⟩
        = some ⟨τ, (σ.pull id htyE') w τ
            ((tableOn_pos expTy hwE).trans hty)⟩ := by
      rw [mixState_neg t σ hwE hv]
      unfold stateOfValuation
      split
      case _ hty' => rw [hty'] at hty; exact absurd hty (by simp)
      case _ τ' hty' =>
        obtain rfl : τ' = τ := by
          rw [hty'] at hty
          exact Option.some.inj hty
        rfl
    show ElVal.valueOf (mixState t σ ⟨w, _⟩) τ _ = σ w τ h
    rw [ElVal.valueOf_congr hstate _ (by simp)]
    rfl

/-! ### The shared admissible region and the witness -/

/-- **The shared admissible region**: the view's region is the image
of the elaboration's under boundary restriction.  `⊇` is the
Catalogue-level soundness of the expansion; `⊆` builds the mixed
expansion point from the completeness witness. -/
theorem ppoly_admRegion_projection :
    AdmRegion expTy mView [ppolyApp]
      = renameTot expTy (restrictCell expTy hsubVE)
          '' AdmRegion expTy mExp ppolyExpH.applications := by
  ext t
  constructor
  · -- the view point extends to an admissible expansion point
    intro ht
    obtain ⟨p, y, hp, hy, hval⟩ := (mem_admRegion_view_iff t).mp ht
    obtain ⟨σ, hσadm, hσp, hσy⟩ := ppoly_expansion_complete hval
    refine ⟨⟨t.1, t.2.1, mixState t σ, mixState_conformant t σ,
      mixState_left t σ, mixState_right t σ⟩, ?_, ?_⟩
    · rw [mem_admRegion_exp_iff]
      show ((toValuation expTy (mixState_conformant t σ)).pull
        id htyE).Admissible
      rw [mixState_pull_eq t σ (hσp.trans hp.symm) (hσy.trans hy.symm)]
      exact hσadm
    · refine alignedTot_ext expTy ?_ ?_ fun w => ?_
      · funext w
        exact congrArg t.1 (Subtype.ext rfl)
      · funext w
        exact congrArg t.2.1 (Subtype.ext rfl)
      · exact mixState_pos t σ (hsubVE w.2) w.2
  · -- an admissible expansion point restricts into the view's region
    rintro ⟨te, hte, rfl⟩
    refine (mem_admRegion_view_iff _).mpr ?_
    have hσadm := (mem_admRegion_exp_iff te).mp hte
    obtain ⟨p, hp⟩ := qscalar_entryE_fin
      (toValuation expTy te.2.2.2.1 0 ⟨[], Dtype.Q⟩
        (vacTy (hsubVE mem_viewApex_0) expTy0))
    obtain ⟨y, hy⟩ := qscalar_entryE_fin
      (toValuation expTy te.2.2.2.1 6 ⟨[], Dtype.Q⟩
        (vacTy (hsubVE mem_viewApex_6) expTy6))
    have hpF : (toValuation expTy te.2.2.2.1).entryFlat 0 0
        = some (.fin p) := by
      rw [Hypernet.Valuation.entryFlat_some
        (toValuation expTy te.2.2.2.1)
        (vacTy (hsubVE mem_viewApex_0) expTy0) 0]
      exact hp
    have hyF : (toValuation expTy te.2.2.2.1).entryFlat 6 0
        = some (.fin y) := by
      rw [Hypernet.Valuation.entryFlat_some
        (toValuation expTy te.2.2.2.1)
        (vacTy (hsubVE mem_viewApex_6) expTy6) 0]
      exact hy
    refine ⟨p, y, ?_, ?_, ?_⟩
    · exact (restrict_entryFlat te mem_viewApex_0 expTy0 0).trans hpF
    · exact (restrict_entryFlat te mem_viewApex_6 expTy6 0).trans hyF
    · refine ppoly_expansion_sound _ hσadm ?_ ?_
      · rw [Hypernet.Valuation.entryFlat_pull]
        exact hpF
      · rw [Hypernet.Valuation.entryFlat_pull]
        exact hyF

/-- **The elaboration law at the packaged-polynomial witness**: θ of
the expansion, marginalized to the view's boundary, is θ of the view.
The single-genus rule's semantic content, machine-checked at its own
live specimen. -/
theorem theta_elab_ppoly :
    dnfPush (renameTot expTy (restrictCell expTy hsubVE))
        (austereDnf expTy mExp ppolyExpH.applications)
      = austereDnf expTy mView [ppolyApp] :=
  theta_elab expTy hsubVE _ _ ppoly_admRegion_projection

end PpolyElab

/-!  ## Axiom receipts (in-package convention: `#print axioms`) -/

end

end SuFunctor

#print axioms SuFunctor.Plain.Joint.exists_push_section
#print axioms SuFunctor.Plain.Pen.push_possWall
#print axioms SuFunctor.theta_elab
#print axioms SuFunctor.PpolyElab.mixState_pull_eq
#print axioms SuFunctor.PpolyElab.ppoly_admRegion_projection
#print axioms SuFunctor.PpolyElab.theta_elab_ppoly
