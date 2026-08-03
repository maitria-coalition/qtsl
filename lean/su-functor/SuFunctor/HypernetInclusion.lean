import Qtsl.HypernetCospan
import Qtsl.SemOkRename
import SuFunctor.SingleSiteSemanticUniverse
import SuFunctor.Plain.CheckerFace

/-! # The possibilistic inclusion of hypernets into the semantic universe

Hypernets — typed wiring diagrams over a wire context — form a decorated
cospan double category: the decoration is the application list, and the
cospan legs label the input and output wires (Fong's decorated cospans;
Patterson, "Structured and decorated cospans from the viewpoint of double
category theory", 2023).  This module mechanizes the *inclusion* of that
reading into the semantic universe (`SuFunctor.SingleSiteSemanticUniverse`): the
transformation θ sending a wiring diagram to its **austere possibilistic
coupling** — the singleton spec presentation whose floor is the
possibilistic wall (`SuFunctor.Plain.possWall`) of its
admissible-valuation region and whose liveness family is the bare
properness demand.

## The stratum

Wire identity is treated as **content-addressed**: distinct wires carry
distinct names globally, a fixed ambient table `ty : Wire → Option
TensorType` assigns each name its type, composition glues along shared
names, and the apex of a composite is the literal union of the parts'
apexes.  The semantic universe's own base is in state-family form
(`DoubleCat.WireSpan`), and the base change sends a wire context to the
**conformant-state family** of its apex — states assigning each wire a
value of its table type.  Conformance is carrier data, not a penalty:
the typed valuation space is the carrier, which is what makes the unit
law below exact.

## Main statements

Writing `G` for the DNF spec functor `SuFunctor.dnfSpecFunctor` and `S`
for the state-family base change described above, the coherence laws of
a tight transformation `θ : F ⟹ S.comp G` out of the hypernet
decoration data are each proved as a standalone theorem, **exactly** —
every comparison is an equality of presentations, never a comparison
cell:

* `vacDnf_comap` / `vacDnf_dnfPull` — the object component (the vacuous
  presentation) is a fixed point of every transport: the naturality
  square of `θ.app`.
* `theta_unit` — θ of the empty diagram is the semantic universe's own
  unit presentation, transported along the canonical carrier comparison
  `idTot`: the `looseApp_laxId` law.
* `theta_comp` — θ of a concatenation is the `dnfBoxplus` composite of
  the θ-images, transported along the canonical split `splitTot` of
  union states: the `looseApp_laxComp` law.  This is the relational
  composition law — admissibility of a glued diagram is the conjunction
  of the parts' — in semantic-universe dress, with **no determinism
  hypothesis**.
* `theta_rename` — θ commutes with renaming cells: the
  `looseApp_natural` law.  The engine is the fourteen-case rename
  transport `PPLC.PrimApp.SemOk_rename`, reached through a *fresh-sink
  extension* (`sinkExtend`): a rename defined on an apex extends to a
  globally type-exact rename by sending every off-apex wire to a fresh
  untyped name.
* `austereDnf_eq_iff` — the kernel of θ on decorations is extensional
  equivalence of admissible regions: two diagrams share a θ-image
  exactly when they admit the same valuations.  The inclusion is
  deliberately non-faithful: syntax and its content addressing live
  upstream; the semantic universe sees the relation.

The wall algebra these consume (`possWall_pull`, `possWall_add`,
`possWall_univ`, `possWall_injective`) is the indicator-penalty
calculus: pullback of a wall is the wall of the preimage, sum is the
wall of the intersection, and walls are determined by their regions
(Dirac witnesses).

The catalogue tie: `Hypernet.Valuation.Admissible` is definitionally the
∀-clause defining the admissible region (`mem_admRegion_iff`), the
typing merge of glued open hypernets over restriction tables is the
union restriction (`mergeWt_tableOn`), and the aligned gluing stratum
(`PPLC.OpenHypernet.glue`, `glue_admissible_iff`, `glue_assoc`) is the
well-formed sub-double-category whose composition `theta_comp` includes.

## The packaging boundary

On the content-addressed presentation the union of two apexes is their
pushout precisely when they overlap only in the shared boundary: union
states always split into agreeing pairs (`splitTot`, total), and
agreeing pairs merge back exactly on that locus (`mergeTot`,
`merge_split`, `split_merge`, under the `hdisj` hypothesis).  Off the
locus, representable name collisions exist, and loose-wise composition
of *cells* would require the copairing out of a genuine pushout, which
the union does not supply — so the aligned representations do not form a
plain pseudo double category under union composition, and the packaged
double functor `∫(S, θ)` (via `CategoryTheory.SpanValued.bmap`) awaits
either a chosen-pushout base or a virtual packaging.  Every semantic
component of the transformation is nonetheless stated and proved here,
at the stratum where content-addressed hypernets live.

## References

* B. Fong, *Decorated cospans*, Theory Appl. Categ. 30 (2015), 1096–1120.
* E. Patterson, *Structured and decorated cospans from the viewpoint of
  double category theory*, arXiv:2304.00447 (2023).
* G.S.H. Cruttwell, M. Lambert, D. Pronk, M. Szyld, *Double fibrations*,
  Theory Appl. Categ. 38 (2022), 1326–1394.
-/

namespace PPLC

/-- Renaming along the identity is the identity. -/
theorem PrimApp.rename_id (a : PrimApp) : a.rename id = a := by
  cases a <;> simp [PrimApp.rename]

/-- Renames agreeing on an application's wires act identically on it. -/
theorem PrimApp.rename_congr {f g : Wire → Wire} (a : PrimApp)
    (h : ∀ w ∈ a.inputWires ++ a.outputWires, f w = g w) :
    a.rename f = a.rename g := by
  have hIn : ∀ w ∈ a.inputWires, f w = g w := fun w hw =>
    h w (List.mem_append_left _ hw)
  have hOut : ∀ w ∈ a.outputWires, f w = g w := fun w hw =>
    h w (List.mem_append_right _ hw)
  cases a <;>
    simp_all [PrimApp.rename, PrimApp.inputWires, PrimApp.outputWires]

end PPLC

namespace SuFunctor

noncomputable section

open CategoryTheory CategoryTheory.WireSpan PPLC
open SuFunctor.Plain SuFunctor.Universe
open scoped NNReal ENNReal

/-! ## Possibilistic wall algebra

The indicator-penalty calculus on `SuFunctor.Plain.possWall`, over an
arbitrary carrier.  These four lemmas are the scalar content of the
inclusion's coherence laws. -/

namespace Plain

universe u

variable {X Y : Type u}

/-- Charged points push forward to charged points: weights are `ℝ≥0`,
so no cancellation can vacate an image point. -/
theorem Joint.mem_support_push {h : X → Y} {μ : Joint X} {w : X}
    (hw : w ∈ μ.wt.support) : h w ∈ (μ.push h).wt.support := by
  classical
  rw [Finsupp.mem_support_iff] at hw ⊢
  rw [Joint.push_wt]
  have hkey : μ.wt.mapDomain h (h w)
      = ∑ a ∈ μ.wt.support, Finsupp.single (h a) (μ.wt a) (h w) := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    rfl
  have hle : μ.wt w ≤ μ.wt.mapDomain h (h w) := by
    rw [hkey]
    have hterm := Finset.single_le_sum
      (f := fun a => Finsupp.single (h a) (μ.wt a) (h w))
      (fun _ _ => zero_le) (Finsupp.mem_support_iff.mpr hw)
    simpa using hterm
  intro hzero
  rw [hzero] at hle
  exact hw (le_antisymm hle zero_le)

/-- The credal set of a region pulls back along pushforward: a joint's
pushforward is supported in `B` iff the joint is supported in the
preimage of `B`. -/
theorem suppIn_push {h : X → Y} {μ : Joint X} {B : Set Y} :
    μ.push h ∈ suppIn B ↔ μ ∈ suppIn (h ⁻¹' B) := by
  classical
  constructor
  · intro hμ w hw
    have : h w ∈ (↑(μ.push h).wt.support : Set Y) := by
      simpa using Joint.mem_support_push (by simpa using hw)
    exact hμ this
  · intro hμ w hw
    have hw' : w ∈ (μ.push h).wt.support := by simpa using hw
    rw [Joint.push_wt] at hw'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hw')
    exact hμ (by simpa using hv)

/-- Pullback of a possibilistic wall is the wall of the preimage. -/
theorem possWall_pull (h : X → Y) (B : Set Y) :
    Pen.pull h (possWall B) = possWall (h ⁻¹' B) := by
  classical
  funext μ
  by_cases hμ : μ.push h ∈ suppIn B
  · rw [Pen.pull_apply, possWall_apply_of_mem hμ,
      possWall_apply_of_mem (suppIn_push.mp hμ)]
  · rw [Pen.pull_apply, possWall_apply_of_notMem hμ,
      possWall_apply_of_notMem fun hc => hμ (suppIn_push.mpr hc)]

/-- The sum of two possibilistic walls is the wall of the intersection. -/
theorem possWall_add (B B' : Set X) :
    possWall B + possWall B' = possWall (B ∩ B') := by
  funext μ
  have hiff : μ ∈ suppIn (B ∩ B') ↔ μ ∈ suppIn B ∧ μ ∈ suppIn B' := by
    simp only [mem_suppIn, Set.subset_inter_iff]
  by_cases h1 : μ ∈ suppIn B <;> by_cases h2 : μ ∈ suppIn B' <;>
    simp [Pi.add_apply, possWall, h1, h2, hiff]

/-- The wall of the full region is the zero penalty. -/
theorem possWall_univ : possWall (Set.univ : Set X) = fun _ => 0 := by
  funext μ
  exact possWall_apply_of_mem fun _ _ => trivial

/-- Walls are determined by their regions: the Dirac joint at any point
separates. -/
theorem possWall_injective {B B' : Set X} (h : possWall B = possWall B') :
    B = B' := by
  have key : ∀ {C C' : Set X}, possWall C = possWall C' → C ⊆ C' := by
    intro C C' hCC' x hx
    have h0 : possWall C' (Joint.dirac x) = 0 := by
      rw [← hCC']
      exact possWall_apply_of_mem (Joint.dirac_mem_suppIn hx)
    have hmem := possWall_eq_zero_iff.mp h0
    rw [mem_suppIn, Joint.dirac_support] at hmem
    simpa using hmem
  exact le_antisymm (key h) (key h.symm)

end Plain

/-! ## The typed carrier

The base change sends a wire context to its conformant-state family:
each wire carries a value of its table type.  This is the typed
valuation space of the context — the carrier the inclusion's couplings
live over. -/

/-- The value stock: a wire state is either absent (an untyped name) or
a typed tensor value. -/
def ElVal : Type := Option (Σ τ : TensorType, TensorValue τ)

/-- Extract the typed value from a state matching a given type. -/
def ElVal.valueOf : (e : ElVal) → (τ : TensorType) →
    e.map Sigma.fst = some τ → TensorValue τ
  | some p, _, h => Option.some.inj h ▸ p.2

/-- Extraction respects equality of states (the value type does not
depend on the state, so this is a plain equality). -/
theorem ElVal.valueOf_congr {e₁ e₂ : ElVal} (he : e₁ = e₂)
    {τ : TensorType} (p₁ : e₁.map Sigma.fst = some τ)
    (p₂ : e₂.map Sigma.fst = some τ) :
    e₁.valueOf τ p₁ = e₂.valueOf τ p₂ := by
  subst he
  rfl

variable (ty : Wire → Option TensorType)

/-- The ambient typing table restricted to a finite wire set. -/
def tableOn (W : Finset Wire) : Wire → Option TensorType :=
  fun w => if w ∈ W then ty w else none

theorem tableOn_pos {W : Finset Wire} {w : Wire} (hw : w ∈ W) :
    tableOn ty W w = ty w := if_pos hw

theorem tableOn_neg {W : Finset Wire} {w : Wire} (hw : w ∉ W) :
    tableOn ty W w = none := if_neg hw

theorem mem_of_tableOn_some {W : Finset Wire} {w : Wire} {τ : TensorType}
    (h : tableOn ty W w = some τ) : w ∈ W := by
  by_contra hw
  rw [tableOn_neg ty hw] at h
  simp at h

/-- The left-biased merge of two restrictions of the ambient table is
the restriction to the union: on a content-addressed namespace the
typing merge of a glued diagram carries no bias at all. -/
theorem mergeWt_tableOn (W₁ W₂ : Finset Wire) :
    mergeWt (tableOn ty W₁) (tableOn ty W₂) = tableOn ty (W₁ ∪ W₂) := by
  funext w
  by_cases h1 : w ∈ W₁
  · cases hty : ty w with
    | none =>
        by_cases h2 : w ∈ W₂ <;>
          simp [mergeWt, tableOn, h1, h2, hty, Finset.mem_union]
    | some τ => simp [mergeWt, tableOn, h1, hty, Finset.mem_union]
  · by_cases h2 : w ∈ W₂ <;>
      simp [mergeWt, tableOn, h1, h2, Finset.mem_union]

/-- The interface of a wire roster, as a state-family base object. -/
def ctxIface (X : Finset Wire) : WireSpan ElVal := ⟨{w : Wire // w ∈ X}⟩

/-- Conformance of a state to the ambient table: each wire's value has
exactly its table type. -/
def Conformant (W : Finset Wire) (s : states (ctxIface W)) : Prop :=
  ∀ w : {w : Wire // w ∈ W}, (s w).map Sigma.fst = ty w.1

/-- Restriction of a state to a sub-roster. -/
def restrictState {W₁ W : Finset Wire} (hsub : W₁ ⊆ W)
    (s : states (ctxIface W)) : states (ctxIface W₁) :=
  fun w => s ⟨w.1, hsub w.2⟩

theorem Conformant.restrict {W₁ W : Finset Wire} (hsub : W₁ ⊆ W)
    {s : states (ctxIface W)} (hs : Conformant ty W s) :
    Conformant ty W₁ (restrictState hsub s) :=
  fun w => hs ⟨w.1, hsub w.2⟩

/-- A fresh wire outside a finite roster (the namespace is infinite). -/
theorem exists_fresh (W : Finset Wire) : ∃ v : Wire, v ∉ W :=
  ⟨W.sup id + 1, fun hmem => by
    have hle : W.sup id + 1 ≤ W.sup id := Finset.le_sup (f := id) hmem
    exact Nat.not_succ_le_self _ hle⟩

/-! ## The valuation bridge

A conformant state of an apex *is* a typed valuation of the catalogue's
vacuum hypernet at the apex table — the mechanized form of "the base
change does not touch carriers". -/

/-- The vacuum hypernet at a wire typing: no applications. -/
def vacNet (wt : Wire → Option TensorType) : Hypernet where
  wireType := wt
  applications := []
  linearity := ⟨List.nodup_nil, List.nodup_nil⟩
  acyclic := fun i => i.elim0
  typeConsistent := fun _ ha => nomatch ha

/-- Read a conformant state as a typed valuation of the apex table. -/
def toValuation {W : Finset Wire} {s : states (ctxIface W)}
    (hs : Conformant ty W s) : (vacNet (tableOn ty W)).Valuation :=
  fun w τ h =>
    have hw : w ∈ W := mem_of_tableOn_some ty h
    (s ⟨w, hw⟩).valueOf τ
      ((hs ⟨w, hw⟩).trans ((tableOn_pos ty hw).symm.trans h))

/-- Reading two propositionally equal wires gives equal values. -/
theorem toValuation_wire_congr {W : Finset Wire} {s : states (ctxIface W)}
    (hs : Conformant ty W s) {w₁ w₂ : Wire} (e : w₁ = w₂) {τ : TensorType}
    (p₁ : (vacNet (tableOn ty W)).wireType w₁ = some τ)
    (p₂ : (vacNet (tableOn ty W)).wireType w₂ = some τ) :
    toValuation ty hs w₁ τ p₁ = toValuation ty hs w₂ τ p₂ := by
  subst e
  rfl

/-- Every typed valuation of an apex table arises from a conformant
state: the reverse leg of the bridge. -/
def stateOfValuation {W : Finset Wire}
    (σ : (vacNet (tableOn ty W)).Valuation) : states (ctxIface W) :=
  fun w =>
    match hty : ty w.1 with
    | none => none
    | some τ => some ⟨τ, σ w.1 τ (by
        show tableOn ty W w.1 = some τ
        rw [tableOn_pos ty w.2, hty])⟩

theorem stateOfValuation_conformant {W : Finset Wire}
    (σ : (vacNet (tableOn ty W)).Valuation) :
    Conformant ty W (stateOfValuation ty σ) := by
  intro w
  show (stateOfValuation ty σ w).map Sigma.fst = ty w.1
  unfold stateOfValuation
  split <;> simp_all

/-- Round trip: reading the state of a valuation recovers the
valuation.  With `stateOfValuation_conformant` this exhibits the typed
valuations of an apex table as exactly the conformant states — the
carrier is untouched by the base change. -/
theorem toValuation_stateOfValuation {W : Finset Wire}
    (σ : (vacNet (tableOn ty W)).Valuation) :
    toValuation ty (stateOfValuation_conformant ty σ) = σ := by
  funext w τ h
  have hw : w ∈ W := mem_of_tableOn_some ty h
  have hty : ty w = some τ := (tableOn_pos ty hw).symm.trans h
  show ElVal.valueOf (stateOfValuation ty σ ⟨w, hw⟩) τ _ = σ w τ h
  have hstate : stateOfValuation ty σ ⟨w, hw⟩
      = some ⟨τ, σ w τ ((tableOn_pos ty hw).trans hty)⟩ := by
    unfold stateOfValuation
    split
    case _ hty' => rw [hty'] at hty; exact absurd hty (by simp)
    case _ τ' hty' =>
      obtain rfl : τ' = τ := by
        rw [hty'] at hty
        exact Option.some.inj hty
      rfl
  rw [ElVal.valueOf_congr hstate _ (by simp)]
  rfl

/-- Round trip, reverse leg: the state built from a conformant state's
valuation-read is the state itself.  With
`toValuation_stateOfValuation` this exhibits the valuation bridge as a
genuine bijection between conformant states and typed valuations. -/
theorem stateOfValuation_toValuation {W : Finset Wire}
    {s : states (ctxIface W)} (hs : Conformant ty W s) :
    stateOfValuation ty (toValuation ty hs) = s := by
  funext w
  have h := hs w
  unfold stateOfValuation
  split
  case _ hty =>
    rw [hty] at h
    cases hsw : s w with
    | none => rfl
    | some p => rw [hsw] at h; simp at h
  case _ τ hty =>
    rw [hty] at h
    cases hsw : s w with
    | none => rw [hsw] at h; simp at h
    | some p =>
      rw [hsw] at h
      have hp : p.1 = τ := by simpa using h
      subst hp
      have hval : toValuation ty hs w.1 p.1
          (by show tableOn ty W w.1 = some p.1
              rw [tableOn_pos ty w.2, hty]) = p.2 := by
        show ElVal.valueOf (s w) p.1 _ = p.2
        rw [ElVal.valueOf_congr hsw _ (by simp)]
        rfl
      rw [hval]

/-! ## The fresh-sink extension

A rename defined on an apex extends to a *globally* type-exact rename by
sending every off-apex wire to a fresh untyped name: the extension
satisfies the hypothesis the fourteen-case rename transport
`PPLC.PrimApp.SemOk_rename` consumes, on the whole namespace. -/

/-- Extend a map by a sink off a roster. -/
def sinkExtend (W : Finset Wire) (h : Wire → Wire) (sink : Wire) :
    Wire → Wire :=
  fun w => if w ∈ W then h w else sink

theorem sinkExtend_pos {W : Finset Wire} {h : Wire → Wire}
    {sink w : Wire} (hw : w ∈ W) : sinkExtend W h sink w = h w :=
  if_pos hw

/-- Type-exactness of the sink extension: if `h` maps `W` into `W'`
preserving the ambient type, its sink extension is type-exact from the
`W'`-table to the `W`-table. -/
theorem sinkExtend_hty {W W' : Finset Wire} {h : Wire → Wire}
    {sink : Wire} (hsink : sink ∉ W')
    (hmem : ∀ w ∈ W, h w ∈ W') (hty_eq : ∀ w ∈ W, ty (h w) = ty w) :
    ∀ w, (vacNet (tableOn ty W')).wireType (sinkExtend W h sink w)
      = (vacNet (tableOn ty W)).wireType w := by
  intro w
  show tableOn ty W' (sinkExtend W h sink w) = tableOn ty W w
  by_cases hw : w ∈ W
  · rw [sinkExtend_pos hw, tableOn_pos ty (hmem w hw), hty_eq w hw,
      tableOn_pos ty hw]
  · rw [show sinkExtend W h sink w = sink from if_neg hw,
      tableOn_neg ty hsink, tableOn_neg ty hw]

/-- Pulling a conformant state's valuation back along a sink-extended
apex map reads the transported state: the valuation bridge commutes
with renaming. -/
theorem toValuation_pull_sinkExtend {W W' : Finset Wire}
    {h : Wire → Wire} {sink : Wire} (hsink : sink ∉ W')
    (hmem : ∀ w ∈ W, h w ∈ W') (hty_eq : ∀ w ∈ W, ty (h w) = ty w)
    {s' : states (ctxIface W')} (hs' : Conformant ty W' s')
    {sh : states (ctxIface W)}
    (hsh : ∀ w : {w : Wire // w ∈ W}, sh w = s' ⟨h w.1, hmem w.1 w.2⟩)
    (hshc : Conformant ty W sh) :
    (toValuation ty hs').pull (sinkExtend W h sink)
        (sinkExtend_hty ty hsink hmem hty_eq)
      = toValuation ty hshc := by
  funext w τ hw
  have hwW : w ∈ W := mem_of_tableOn_some ty (h := hw)
  show toValuation ty hs' (sinkExtend W h sink w) τ _ = _
  rw [toValuation_wire_congr ty hs' (sinkExtend_pos hwW)
    _ (by
      show tableOn ty W' (h w) = some τ
      rw [tableOn_pos ty (hmem w hwW), hty_eq w hwW,
        ← tableOn_pos ty (W := W) hwW]
      exact hw)]
  show ElVal.valueOf (s' ⟨h w, hmem w hwW⟩) τ _
    = ElVal.valueOf (sh ⟨w, hwW⟩) τ _
  exact ElVal.valueOf_congr (hsh ⟨w, hwW⟩).symm _ _

/-- Block-restriction congruence of the semantic clause: an
application's clause reads the same on a state and on its restriction
to any sub-roster containing the application's wires.  This is the
rename transport at the sink extension of the identity. -/
theorem semOk_restrict {W₁ W : Finset Wire} (hsub : W₁ ⊆ W)
    {s : states (ctxIface W)} (hs : Conformant ty W s) {a : PrimApp}
    (hTC : a.TypeConsistent (tableOn ty W₁))
    (hwires : ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ W₁) :
    a.SemOk (toValuation ty hs) ↔
      a.SemOk (toValuation ty (hs.restrict ty hsub)) := by
  obtain ⟨sink, hsink⟩ := exists_fresh W
  have hmem : ∀ w ∈ W₁, id w ∈ W := fun w hw => hsub hw
  have hty_eq : ∀ w ∈ W₁, ty (id w) = ty w := fun w _ => rfl
  have hpull := toValuation_pull_sinkExtend ty (h := id) hsink hmem hty_eq
    hs (sh := restrictState hsub s) (fun w => rfl) (hs.restrict ty hsub)
  have h1 := PrimApp.SemOk_rename (sinkExtend W₁ id sink)
    (sinkExtend_hty ty hsink hmem hty_eq) (toValuation ty hs) a hTC
  rw [hpull] at h1
  have hren : a.rename (sinkExtend W₁ id sink) = a :=
    (PrimApp.rename_congr a fun w hw =>
      sinkExtend_pos (hwires w hw)).trans (PrimApp.rename_id a)
  rw [hren] at h1
  exact h1

/-! ## Aligned open contexts and their state families -/

/-- An aligned loose arrow between rosters: an apex containing both
feet.  On a content-addressed namespace this *is* a cospan of wire
contexts — the legs are the subset inclusions. -/
structure AlignedLoose (X Y : Finset Wire) where
  /-- The apex wire set. -/
  apex : Finset Wire
  /-- The input leg. -/
  left_le : X ⊆ apex
  /-- The output leg. -/
  right_le : Y ⊆ apex

variable {X Y Z X' Y' : Finset Wire}

/-- Sequential composition of aligned looses: union of apexes (the
pushout of content-addressed wire sets, on the seam-disjoint locus). -/
def AlignedLoose.seq (m : AlignedLoose X Y) (n : AlignedLoose Y Z) :
    AlignedLoose X Z where
  apex := m.apex ∪ n.apex
  left_le := m.left_le.trans Finset.subset_union_left
  right_le := n.right_le.trans Finset.subset_union_right

/-- The loose identity: a roster as its own apex. -/
def AlignedLoose.unit (X : Finset Wire) : AlignedLoose X X :=
  ⟨X, Finset.Subset.refl X, Finset.Subset.refl X⟩

/-- The state family of an aligned loose: conformant apex states,
fibred over their boundary restrictions.  This is the base change on
loose arrows: the typed valuation space of the apex, marginalized to
the feet. -/
def alignedPat (m : AlignedLoose X Y) :
    Pat (ctxIface X) (ctxIface Y) :=
  fun x y =>
    { s : states (ctxIface m.apex) //
        Conformant ty m.apex s ∧
        (∀ w : {w : Wire // w ∈ X}, s ⟨w.1, m.left_le w.2⟩ = x w) ∧
        (∀ w : {w : Wire // w ∈ Y}, s ⟨w.1, m.right_le w.2⟩ = y w) }

/-- Extensionality for total points of an aligned state family. -/
theorem alignedTot_ext {m : AlignedLoose X Y}
    {t t' : Pat.Tot (alignedPat ty m)}
    (hx : t.1 = t'.1) (hy : t.2.1 = t'.2.1)
    (hs : ∀ w, t.2.2.1 w = t'.2.2.1 w) : t = t' := by
  obtain ⟨x, y, s, hp⟩ := t
  obtain ⟨x', y', s', hp'⟩ := t'
  cases hx
  cases hy
  obtain rfl : s = s' := funext hs
  rfl

/-- Split a conformant union state into its agreeing pair: the laxator
of the base change, total on all representations. -/
def splitTot (m : AlignedLoose X Y) (n : AlignedLoose Y Z) :
    Pat.Tot (alignedPat ty (m.seq n)) →
      Pat.Tot (Pat.comp (alignedPat ty m) (alignedPat ty n)) :=
  fun t =>
    ⟨t.1, t.2.1,
      fun w => t.2.2.1 ⟨w.1, Finset.subset_union_left (m.right_le w.2)⟩,
      ⟨restrictState Finset.subset_union_left t.2.2.1,
        (t.2.2.2.1).restrict ty Finset.subset_union_left,
        fun w => t.2.2.2.2.1 w,
        fun _ => rfl⟩,
      ⟨restrictState Finset.subset_union_right t.2.2.1,
        (t.2.2.2.1).restrict ty Finset.subset_union_right,
        fun _ => rfl,
        fun w => t.2.2.2.2.2 w⟩⟩

/-- Merge an agreeing pair into a union state — defined on all pairs,
inverse to the split exactly on the seam-disjoint locus (`hdisj`),
where the union is the genuine pushout. -/
def mergeTot (m : AlignedLoose X Y) (n : AlignedLoose Y Z)
    (hdisj : ∀ w ∈ m.apex, w ∈ n.apex → w ∈ Y) :
    Pat.Tot (Pat.comp (alignedPat ty m) (alignedPat ty n)) →
      Pat.Tot (alignedPat ty (m.seq n)) :=
  fun t =>
    ⟨t.1, t.2.1,
      fun w =>
        if h : w.1 ∈ m.apex then t.2.2.2.1.1 ⟨w.1, h⟩
        else t.2.2.2.2.1 ⟨w.1, (Finset.mem_union.mp w.2).resolve_left h⟩,
      by
        intro w
        by_cases h : w.1 ∈ m.apex
        · simpa [h] using t.2.2.2.1.2.1 ⟨w.1, h⟩
        · simpa [h] using t.2.2.2.2.2.1
            ⟨w.1, (Finset.mem_union.mp w.2).resolve_left h⟩,
      by
        intro w
        have h : w.1 ∈ m.apex := m.left_le w.2
        simpa [h] using t.2.2.2.1.2.2.1 w,
      by
        intro w
        have hn : w.1 ∈ n.apex := n.right_le w.2
        by_cases h : w.1 ∈ m.apex
        · have hY : w.1 ∈ Y := hdisj w.1 h hn
          have h1 : t.2.2.2.1.1 ⟨w.1, h⟩ = t.2.2.1 ⟨w.1, hY⟩ :=
            t.2.2.2.1.2.2.2 ⟨w.1, hY⟩
          have h2 : t.2.2.2.2.1 ⟨w.1, hn⟩ = t.2.2.1 ⟨w.1, hY⟩ :=
            t.2.2.2.2.2.2.1 ⟨w.1, hY⟩
          have h3 : t.2.2.2.2.1 ⟨w.1, hn⟩ = t.2.1 w :=
            t.2.2.2.2.2.2.2 w
          simpa [h] using h1.trans (h2.symm.trans h3)
        · simpa [h] using t.2.2.2.2.2.2.2 w⟩

/-- Merging after splitting is the identity: the split loses nothing. -/
theorem merge_split (m : AlignedLoose X Y) (n : AlignedLoose Y Z)
    (hdisj : ∀ w ∈ m.apex, w ∈ n.apex → w ∈ Y)
    (t : Pat.Tot (alignedPat ty (m.seq n))) :
    mergeTot ty m n hdisj (splitTot ty m n t) = t := by
  refine alignedTot_ext ty rfl rfl fun w => ?_
  show (if h : w.1 ∈ m.apex
      then restrictState Finset.subset_union_left t.2.2.1 ⟨w.1, h⟩
      else restrictState Finset.subset_union_right t.2.2.1
        ⟨w.1, (Finset.mem_union.mp w.2).resolve_left h⟩)
    = t.2.2.1 w
  by_cases h : w.1 ∈ m.apex
  · rw [dif_pos h]; rfl
  · rw [dif_neg h]; rfl

/-- Extensionality for total points of a composite state family. -/
theorem compTot_ext {m : AlignedLoose X Y} {n : AlignedLoose Y Z}
    {p p' : Pat.Tot (Pat.comp (alignedPat ty m) (alignedPat ty n))}
    (hx : p.1 = p'.1) (hz : p.2.1 = p'.2.1)
    (hy : ∀ w, p.2.2.1 w = p'.2.2.1 w)
    (hm : ∀ w, p.2.2.2.1.1 w = p'.2.2.2.1.1 w)
    (hn : ∀ w, p.2.2.2.2.1 w = p'.2.2.2.2.1 w) : p = p' := by
  obtain ⟨x, z, y, ⟨sm, pm⟩, ⟨sn, pn⟩⟩ := p
  obtain ⟨x', z', y', ⟨sm', pm'⟩, ⟨sn', pn'⟩⟩ := p'
  cases hx
  cases hz
  obtain rfl : y = y' := funext hy
  obtain rfl : sm = sm' := funext hm
  obtain rfl : sn = sn' := funext hn
  rfl

/-- Splitting after merging is the identity, on the seam-disjoint
locus: the union is the pushout exactly there. -/
theorem split_merge (m : AlignedLoose X Y) (n : AlignedLoose Y Z)
    (hdisj : ∀ w ∈ m.apex, w ∈ n.apex → w ∈ Y)
    (p : Pat.Tot (Pat.comp (alignedPat ty m) (alignedPat ty n))) :
    splitTot ty m n (mergeTot ty m n hdisj p) = p := by
  refine compTot_ext ty rfl rfl (fun w => ?_) (fun w => ?_) (fun w => ?_)
  · -- middle boundary
    show (if h : w.1 ∈ m.apex
        then p.2.2.2.1.1 ⟨w.1, h⟩
        else p.2.2.2.2.1 ⟨w.1, _⟩) = p.2.2.1 w
    rw [dif_pos (m.right_le w.2)]
    exact p.2.2.2.1.2.2.2 w
  · -- left component
    show (if h : w.1 ∈ m.apex
        then p.2.2.2.1.1 ⟨w.1, h⟩
        else p.2.2.2.2.1 ⟨w.1, _⟩) = p.2.2.2.1.1 w
    rw [dif_pos w.2]
    exact congrArg p.2.2.2.1.1 (Subtype.ext rfl)
  · -- right component
    show (if h : w.1 ∈ m.apex
        then p.2.2.2.1.1 ⟨w.1, h⟩
        else p.2.2.2.2.1 ⟨w.1, _⟩) = p.2.2.2.2.1 w
    by_cases h : w.1 ∈ m.apex
    · rw [dif_pos h]
      have hY : w.1 ∈ Y := hdisj w.1 h w.2
      have h1 : p.2.2.2.1.1 ⟨w.1, h⟩ = p.2.2.1 ⟨w.1, hY⟩ :=
        p.2.2.2.1.2.2.2 ⟨w.1, hY⟩
      have h2 : p.2.2.2.2.1 ⟨w.1, w.2⟩ = p.2.2.1 ⟨w.1, hY⟩ :=
        p.2.2.2.2.2.2.1 ⟨w.1, hY⟩
      exact h1.trans h2.symm
    · rw [dif_neg h]
      exact congrArg p.2.2.2.2.1 (Subtype.ext rfl)

/-- The carrier comparison at a loose identity: a conformant state of a
roster-as-apex determines a diagonal point (its two boundary
restrictions coincide). -/
def idTot (X : Finset Wire) :
    Pat.Tot (alignedPat ty (AlignedLoose.unit X)) →
      Pat.Tot (Pat.id (ctxIface X)) :=
  fun t =>
    ⟨t.1, t.2.1,
      ⟨⟨funext fun w => (t.2.2.2.2.1 w).symm.trans (t.2.2.2.2.2 w)⟩⟩⟩

/-- A renaming cell between aligned looses: an apex map preserving the
ambient type and the feet.  The induced boundary tights are its
restrictions. -/
structure AlignedCell (m : AlignedLoose X Y) (m' : AlignedLoose X' Y')
    where
  /-- The apex wire map. -/
  map : Wire → Wire
  /-- Apexes map to apexes. -/
  mem : ∀ w ∈ m.apex, map w ∈ m'.apex
  /-- The ambient type is preserved on the apex. -/
  ty_eq : ∀ w ∈ m.apex, ty (map w) = ty w
  /-- Input feet map to input feet. -/
  left_mem : ∀ w ∈ X, map w ∈ X'
  /-- Output feet map to output feet. -/
  right_mem : ∀ w ∈ Y, map w ∈ Y'

/-- The state transport of a renaming cell: contravariant on conformant
states, over the boundary restrictions. -/
def renameTot {m : AlignedLoose X Y} {m' : AlignedLoose X' Y'}
    (c : AlignedCell ty m m') :
    Pat.Tot (alignedPat ty m') → Pat.Tot (alignedPat ty m) :=
  fun t =>
    ⟨fun w => t.1 ⟨c.map w.1, c.left_mem w.1 w.2⟩,
     fun w => t.2.1 ⟨c.map w.1, c.right_mem w.1 w.2⟩,
     fun w => t.2.2.1 ⟨c.map w.1, c.mem w.1 w.2⟩,
     by
       intro w
       rw [show ty w.1 = ty (c.map w.1) from (c.ty_eq w.1 w.2).symm]
       exact t.2.2.2.1 ⟨c.map w.1, c.mem w.1 w.2⟩,
     fun w => t.2.2.2.2.1 ⟨c.map w.1, c.left_mem w.1 w.2⟩,
     fun w => t.2.2.2.2.2 ⟨c.map w.1, c.right_mem w.1 w.2⟩⟩

/-! ## Admissibility regions -/

/-- The admissible region of a raw application list over an aligned
loose: the total points whose valuation satisfies every application.
Membership is definitionally the catalogue's admissibility clause
(`PPLC.Hypernet.Valuation.Admissible`), read at the apex table. -/
def AdmRegion (m : AlignedLoose X Y) (T : List PrimApp) :
    Set (Pat.Tot (alignedPat ty m)) :=
  {t | ∀ a ∈ T, a.SemOk (toValuation ty t.2.2.2.1)}

theorem mem_admRegion_iff {m : AlignedLoose X Y} {T : List PrimApp}
    {t : Pat.Tot (alignedPat ty m)} :
    t ∈ AdmRegion ty m T ↔
      ∀ a ∈ T, a.SemOk (toValuation ty t.2.2.2.1) :=
  Iff.rfl

/-- The empty diagram admits every valuation. -/
theorem admRegion_nil (m : AlignedLoose X Y) :
    AdmRegion ty m [] = Set.univ :=
  Set.eq_univ_of_forall fun _ _ ha => nomatch ha

/-- **The relational composition law** (no determinism hypothesis): the
admissible region of a concatenation is the intersection of the parts'
regions, each read through its projection of the split.  `cell`'s
disjunctive clause passes through the conjunction untouched. -/
theorem admRegion_append (m : AlignedLoose X Y) (n : AlignedLoose Y Z)
    (T₁ T₂ : List PrimApp)
    (hTC₁ : ∀ a ∈ T₁, a.TypeConsistent (tableOn ty m.apex))
    (hw₁ : ∀ a ∈ T₁, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ m.apex)
    (hTC₂ : ∀ a ∈ T₂, a.TypeConsistent (tableOn ty n.apex))
    (hw₂ : ∀ a ∈ T₂, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ n.apex) :
    AdmRegion ty (m.seq n) (T₁ ++ T₂)
      = splitTot ty m n ⁻¹'
          (Pat.compFst (alignedPat ty m) (alignedPat ty n) ⁻¹'
              AdmRegion ty m T₁
            ∩ Pat.compSnd (alignedPat ty m) (alignedPat ty n) ⁻¹'
              AdmRegion ty n T₂) := by
  ext t
  simp only [Set.mem_preimage, Set.mem_inter_iff, mem_admRegion_iff]
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · exact (semOk_restrict ty Finset.subset_union_left t.2.2.2.1
        (hTC₁ a ha) (hw₁ a ha)).mp (h a (List.mem_append_left _ ha))
    · exact (semOk_restrict ty Finset.subset_union_right t.2.2.2.1
        (hTC₂ a ha) (hw₂ a ha)).mp (h a (List.mem_append_right _ ha))
  · rintro ⟨h₁, h₂⟩ a ha
    rcases List.mem_append.mp ha with hm | hn
    · exact (semOk_restrict ty Finset.subset_union_left t.2.2.2.1
        (hTC₁ a hm) (hw₁ a hm)).mpr (h₁ a hm)
    · exact (semOk_restrict ty Finset.subset_union_right t.2.2.2.1
        (hTC₂ a hn) (hw₂ a hn)).mpr (h₂ a hn)

/-- **Rename transport of admissible regions**: the preimage of a
region under a renaming cell's state transport is the region of the
renamed list.  The engine is `PPLC.PrimApp.SemOk_rename` at the
fresh-sink extension of the cell's map. -/
theorem admRegion_rename {m : AlignedLoose X Y} {m' : AlignedLoose X' Y'}
    (c : AlignedCell ty m m') (T : List PrimApp)
    (hTC : ∀ a ∈ T, a.TypeConsistent (tableOn ty m.apex))
    (hw : ∀ a ∈ T, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ m.apex) :
    renameTot ty c ⁻¹' AdmRegion ty m T
      = AdmRegion ty m' (T.map (PrimApp.rename c.map)) := by
  ext t
  simp only [Set.mem_preimage, mem_admRegion_iff, List.forall_mem_map]
  refine forall₂_congr fun a ha => ?_
  obtain ⟨sink, hsink⟩ := exists_fresh m'.apex
  have hpull := toValuation_pull_sinkExtend ty (h := c.map) hsink
    (fun w hw' => c.mem w hw') (fun w hw' => c.ty_eq w hw')
    t.2.2.2.1 (sh := fun w => t.2.2.1 ⟨c.map w.1, c.mem w.1 w.2⟩)
    (fun w => rfl) (renameTot ty c t).2.2.2.1
  have h1 := PrimApp.SemOk_rename (sinkExtend m.apex c.map sink)
    (sinkExtend_hty ty hsink (fun w hw' => c.mem w hw')
      (fun w hw' => c.ty_eq w hw'))
    (toValuation ty t.2.2.2.1) a (hTC a ha)
  rw [hpull] at h1
  rw [PrimApp.rename_congr a
    (fun w hw' => sinkExtend_pos (hw a ha w hw')) ] at h1
  exact h1.symm

/-! ## The transformation θ -/

/-- The vacuous atom: zero floor, bare properness demand. -/
def vacAtom (K : Type) : SpecAtom K where
  floor := fun _ => 0
  marks := {⊤}
  finite_marks := Set.finite_singleton _
  top_mem := rfl

/-- The vacuous presentation: θ's object component. -/
def vacDnf (K : Type) : SpecDnf K :=
  ⟨{vacAtom K}, Set.finite_singleton _⟩

/-- The vacuous presentation is a fixed point of every transport: the
naturality square of θ's object component. -/
theorem vacDnf_comap {K K' : Type} (g : K' → K) :
    (vacDnf K).comap g = vacDnf K' := by
  refine SpecDnf.ext ?_
  rw [SpecDnf.comap_atoms, show (vacDnf K).atoms = {vacAtom K} from rfl,
    Set.image_singleton]
  refine congrArg _ (SpecAtom.ext rfl ?_)
  rw [SpecAtom.comap_marks, show (vacAtom K).marks = {⊤} from rfl,
    Set.image_singleton]
  refine congrArg _ ?_
  funext x
  simp [Pi.top_apply]

/-- The object naturality, in the semantic universe's own transport. -/
theorem vacDnf_dnfPull {A B : Type} (h : A → B) :
    dnfPull h (vacDnf (Plain.Joint B)) = vacDnf (Plain.Joint A) :=
  vacDnf_comap (Plain.Joint.push h)

/-- The austere possibilistic atom of a raw diagram: the wall of its
admissible region, with the bare properness demand. -/
def austereAtom (m : AlignedLoose X Y) (T : List PrimApp) :
    SpecAtom (Plain.Joint (Pat.Tot (alignedPat ty m))) where
  floor := possWall (AdmRegion ty m T)
  marks := {⊤}
  finite_marks := Set.finite_singleton _
  top_mem := rfl

/-- θ's loose component: the austere possibilistic coupling of a raw
diagram. -/
def austereDnf (m : AlignedLoose X Y) (T : List PrimApp) :
    SpecDnf (Plain.Joint (Pat.Tot (alignedPat ty m))) :=
  ⟨{austereAtom ty m T}, Set.finite_singleton _⟩

/-- Transport of the properness mark is the properness mark. -/
theorem pull_top_singleton {A B : Type} (g : A → B) :
    Pen.pull g '' ({⊤} : Set (Pen B)) = {⊤} := by
  rw [Set.image_singleton]
  refine congrArg _ ?_
  funext μ
  simp [Pen.pull_apply, Pi.top_apply]

/-- **The unit law, exactly**: θ of the empty diagram is the semantic
universe's own unit presentation, transported along the carrier
comparison.  Both sides are the vacuous atom — conformance lives in the
carrier, so the empty diagram costs nothing. -/
theorem theta_unit (X : Finset Wire) :
    dnfPull (idTot ty X) (dnfUnit (ctxIface X))
      = austereDnf ty (AlignedLoose.unit X) [] := by
  refine SpecDnf.ext ?_
  rw [dnfPull_atoms, show (dnfUnit (ctxIface X)).atoms
      = {unitAtom (ctxIface X)} from rfl, Set.image_singleton]
  refine congrArg _ (SpecAtom.ext ?_ ?_)
  · show Pen.pull (idTot ty X) (unitPen (ctxIface X))
      = possWall (AdmRegion ty (AlignedLoose.unit X) [])
    rw [admRegion_nil, Plain.possWall_univ]
    rfl
  · show Pen.pull (idTot ty X) '' (unitAtom (ctxIface X)).marks
      = ({⊤} : Set (Pen (Pat.Tot (alignedPat ty (AlignedLoose.unit X)))))
    rw [show (unitAtom (ctxIface X)).marks = {⊤} from rfl]
    exact pull_top_singleton _

/-- **The composition law, exactly (β = 1)**: θ of a concatenation is
the semantic universe's compositor applied to the θ-images, transported
along the canonical split.  The floor computation is the possibilistic
algebra — pushforward-then-add of two walls is the wall of the
intersection of preimages — composed with the relational composition
law; no determinism hypothesis appears. -/
theorem theta_comp (m : AlignedLoose X Y) (n : AlignedLoose Y Z)
    (T₁ T₂ : List PrimApp)
    (hTC₁ : ∀ a ∈ T₁, a.TypeConsistent (tableOn ty m.apex))
    (hw₁ : ∀ a ∈ T₁, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ m.apex)
    (hTC₂ : ∀ a ∈ T₂, a.TypeConsistent (tableOn ty n.apex))
    (hw₂ : ∀ a ∈ T₂, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ n.apex) :
    dnfPull (splitTot ty m n)
        (dnfBoxplus (austereDnf ty m T₁) (austereDnf ty n T₂))
      = austereDnf ty (m.seq n) (T₁ ++ T₂) := by
  refine SpecDnf.ext ?_
  rw [dnfPull_atoms,
    show (dnfBoxplus (austereDnf ty m T₁) (austereDnf ty n T₂)).atoms
      = Set.image2 atomBoxplus {austereAtom ty m T₁} {austereAtom ty n T₂}
      from rfl,
    Set.image2_singleton, Set.image_singleton]
  refine congrArg _ (SpecAtom.ext ?_ ?_)
  · show Pen.pull (splitTot ty m n)
        (boxplus (possWall (AdmRegion ty m T₁))
          (possWall (AdmRegion ty n T₂)))
      = possWall (AdmRegion ty (m.seq n) (T₁ ++ T₂))
    have hbox : boxplus (M := alignedPat ty m) (N := alignedPat ty n)
        (possWall (AdmRegion ty m T₁)) (possWall (AdmRegion ty n T₂))
        = possWall
            (Pat.compFst (alignedPat ty m) (alignedPat ty n) ⁻¹'
                AdmRegion ty m T₁
              ∩ Pat.compSnd (alignedPat ty m) (alignedPat ty n) ⁻¹'
                AdmRegion ty n T₂) := by
      rw [show boxplus (M := alignedPat ty m) (N := alignedPat ty n)
            (possWall (AdmRegion ty m T₁)) (possWall (AdmRegion ty n T₂))
          = Pen.pull (Pat.compFst (alignedPat ty m) (alignedPat ty n))
              (possWall (AdmRegion ty m T₁))
            + Pen.pull (Pat.compSnd (alignedPat ty m) (alignedPat ty n))
              (possWall (AdmRegion ty n T₂)) from rfl,
        Plain.possWall_pull, Plain.possWall_pull, Plain.possWall_add]
    rw [hbox, Plain.possWall_pull,
      admRegion_append ty m n T₁ T₂ hTC₁ hw₁ hTC₂ hw₂]
  · show Pen.pull (splitTot ty m n) ''
        (atomBoxplus (austereAtom ty m T₁) (austereAtom ty n T₂)).marks
      = ({⊤} : Set (Pen (Pat.Tot (alignedPat ty (m.seq n)))))
    rw [atomBoxplus_marks,
      show (austereAtom ty m T₁).marks = {⊤} from rfl,
      show (austereAtom ty n T₂).marks = {⊤} from rfl,
      pull_top_singleton, pull_top_singleton, Set.union_self]
    exact pull_top_singleton _

/-- **The naturality law, exactly (ψ = 1)**: θ commutes with renaming
cells — transport of the austere coupling is the austere coupling of
the renamed diagram. -/
theorem theta_rename {m : AlignedLoose X Y} {m' : AlignedLoose X' Y'}
    (c : AlignedCell ty m m') (T : List PrimApp)
    (hTC : ∀ a ∈ T, a.TypeConsistent (tableOn ty m.apex))
    (hw : ∀ a ∈ T, ∀ w ∈ a.inputWires ++ a.outputWires, w ∈ m.apex) :
    dnfPull (renameTot ty c) (austereDnf ty m T)
      = austereDnf ty m' (T.map (PrimApp.rename c.map)) := by
  refine SpecDnf.ext ?_
  rw [dnfPull_atoms, show (austereDnf ty m T).atoms
      = {austereAtom ty m T} from rfl, Set.image_singleton]
  refine congrArg _ (SpecAtom.ext ?_ ?_)
  · show Pen.pull (renameTot ty c) (possWall (AdmRegion ty m T))
      = possWall (AdmRegion ty m' (T.map (PrimApp.rename c.map)))
    rw [Plain.possWall_pull, admRegion_rename ty c T hTC hw]
  · show Pen.pull (renameTot ty c) '' (austereAtom ty m T).marks
      = ({⊤} : Set (Pen (Pat.Tot (alignedPat ty m'))))
    rw [show (austereAtom ty m T).marks = {⊤} from rfl]
    exact pull_top_singleton _

/-- **The kernel of θ is extensional equivalence**: two diagrams share
an austere coupling exactly when they admit the same valuations.  The
inclusion is deliberately non-faithful — the semantic universe sees the
relation, never the syntax. -/
theorem austereDnf_eq_iff (m : AlignedLoose X Y) (T T' : List PrimApp) :
    austereDnf ty m T = austereDnf ty m T'
      ↔ AdmRegion ty m T = AdmRegion ty m T' := by
  constructor
  · intro h
    have hatom : austereAtom ty m T = austereAtom ty m T' := by
      have h1 := congrArg SpecDnf.atoms h
      rw [show (austereDnf ty m T).atoms = {austereAtom ty m T} from rfl,
        show (austereDnf ty m T').atoms = {austereAtom ty m T'} from rfl,
        Set.singleton_eq_singleton_iff] at h1
      exact h1
    exact Plain.possWall_injective (congrArg SpecAtom.floor hatom)
  · intro h
    refine SpecDnf.ext ?_
    show {austereAtom ty m T} = {austereAtom ty m T'}
    refine congrArg _ (SpecAtom.ext ?_ rfl)
    show possWall (AdmRegion ty m T) = possWall (AdmRegion ty m T')
    rw [h]

/-!  ## Axiom receipts (in-package convention: `#print axioms`) -/

end

end SuFunctor

#print axioms SuFunctor.Plain.possWall_pull
#print axioms SuFunctor.Plain.possWall_add
#print axioms SuFunctor.Plain.possWall_injective
#print axioms SuFunctor.semOk_restrict
#print axioms SuFunctor.merge_split
#print axioms SuFunctor.split_merge
#print axioms SuFunctor.admRegion_append
#print axioms SuFunctor.admRegion_rename
#print axioms SuFunctor.vacDnf_dnfPull
#print axioms SuFunctor.theta_unit
#print axioms SuFunctor.theta_comp
#print axioms SuFunctor.theta_rename
#print axioms SuFunctor.austereDnf_eq_iff
#print axioms SuFunctor.toValuation_stateOfValuation
#print axioms SuFunctor.stateOfValuation_toValuation
