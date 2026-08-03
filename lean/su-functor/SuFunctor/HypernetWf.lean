import SuFunctor.HypernetDouble

/-! # The well-formed fragment of the double category of open hypernets

`SuFunctor.HypernetDouble` constructs the double category `HNet` of open
hypernets at the content-addressed stratum: loose arrows are aligned
cospans of wire rosters decorated with **raw** wiring diagrams —
type-consistent, apex-supported application lists, with no linearity or
single-assignment discipline.  The hypernets of the certificate calculus
are not raw: linearity, single static assignment, and the interface
discipline carve a fragment.  This module mechanizes that fragment and
its closure, as the roster-form counterpart of the well-formedness
clauses and gluing theorem of `Qtsl.HypernetCospan`
(`PPLC.OpenHypernet.glue` — the wf-closure theorem at the aligned
stratum).

## The clauses

A decorated loose arrow with feet `X, Y` and diagram `T` is
**well-formed** (`IsWf`) when:

* *linearity* — no wire is consumed twice or produced twice
  (`PPLC.Linearity`);
* *single assignment* — every application consumes only wires produced
  strictly earlier or produced by none (`PPLC.Acyclic`);
* *inputs* — input wires are produced by no application, and every
  consumed-but-unproduced wire is an input;
* *outputs* — output wires are consumed by no application (exposure is
  the consumption), and every output is produced or passes through from
  the inputs.

The clause pattern of the cospan literature would also demand that the
interface legs be monic; here that is structural — feet are finite sets
and legs are literal inclusions — so no clause carries it.  Apex support
and type consistency are likewise not clauses: they are already bundled
in the decoration type `HDec`.

## Closure on the seam-disjoint locus

Well-formedness is **not** closed under unrestricted loose composition:
two well-formed diagrams may each touch the same junk-overlap wire
outside the shared boundary, and the concatenation then breaks
linearity.  At the aligned stratum the union of two apexes is their
pushout precisely on the **seam-disjoint locus** — apex overlap
contained in the shared boundary — which is what distinct content
addresses guarantee for encoded hypernets.  On that locus the fragment
is closed (`IsWf.glue`), and the loose identities are well-formed
(`isWf_unit`): the well-formed decorated looses, with all cells between
them, form the sub-double-category of open hypernets of the certificate
calculus, composable exactly where the aligned stratum is
pushout-normal.

The locus hypothesis is the *same* hypothesis under which the packaged
inclusion's compositor laxators invert
(`SuFunctor.hnetInclusion_laxComp_isInvertible`): one condition carves
both the fragment's composability discipline and the inclusion's
strictness locus, because both say "the union is the pushout".  In
particular the inclusion restricts to the well-formed fragment with its
composition comparison invertible at every composite the fragment
licenses; no separate statement is needed, and none is made.

Well-formedness is deliberately **not** closed under pushforward along
arbitrary cells (the discrete-opfibration transport of `hnetProj`):
enlarging the input foot past a produced wire breaks the inputs clause.
The fragment is carved by looses, not transported.

## The adapter

The bridge to the landed closure theorem is `IsWf.toOpen`, packaging a
well-formed decorated loose as a `PPLC.OpenHypernet` (interfaces are the
feet's element lists; the wire typing is the ambient table restricted to
the apex).  Composability of well-formed parts on the locus yields the
aligned-gluing hypotheses (`toOpen_aligned`) — the seam is literal name
sharing, typing compatibility is automatic because both typings restrict
the one ambient table — and every clause of the composite is a field of
the landed `PPLC.OpenHypernet.glue`, pulled back through the adapter
(`IsWf.glue`).  The adapter intertwines composition and units on the
nose: `toOpen_glue`, `toOpen_unit`.

## Main definitions and results

* `IsWf` — the well-formedness clauses, in roster form.
* `IsWf.toOpen` — the packaging of a well-formed decorated loose as an
  open hypernet, with `toOpen_aligned` producing the gluing hypotheses
  on the seam-disjoint locus.
* `isWf_unit`, `IsWf.glue` — the fragment contains the loose units and
  is closed under loose composition on the locus.
* `toOpen_glue`, `toOpen_unit` — the adapter sends loose composition to
  gluing and loose units to the loose identity, on the nose.
* `IsWfLoose`, `isWfLoose_id`, `IsWfLoose.comp` — the same three facts
  at the level of the double category `HNet` itself: the predicate on
  its loose arrows, satisfied by identities and preserved by
  composition on the locus.

## References

* B. Fong, *Decorated cospans*, Theory Appl. Categ. 30 (2015), 1096–1120.
* E. Patterson, *Structured and decorated cospans from the viewpoint of
  double category theory*, arXiv:2304.00447 (2023).
-/

namespace SuFunctor

open CategoryTheory PPLC

/-- Well-formedness of a wiring diagram `T` between feet `X` and `Y`:
linearity, single static assignment, and the interface discipline of
the monogamous genre.  Interface-leg monicity is structural (feet are
finite sets, legs are inclusions); apex support and type consistency
are carried by the decoration type `HDec`, not repeated here. -/
structure IsWf (X Y : Finset Wire) (T : List PrimApp) : Prop where
  /-- No wire is consumed twice or produced twice. -/
  linear : Linearity T
  /-- Consumed wires are produced strictly earlier, or produced by
  none. -/
  ssa : Acyclic T
  /-- Input wires are produced by no application. -/
  inputs_unproduced : ∀ w ∈ X, w ∉ producedW T
  /-- Every consumed-but-unproduced wire is an input. -/
  consumed_covered : ∀ w ∈ consumedW T, w ∉ producedW T → w ∈ X
  /-- Output wires are consumed by no application: exposure is the
  consumption. -/
  outputs_unconsumed : ∀ w ∈ Y, w ∉ consumedW T
  /-- Every output is produced, or passes through from the inputs. -/
  outputs_grounded : ∀ w ∈ Y, w ∈ producedW T ∨ w ∈ X

variable (ty : Wire → Option TensorType)

/-! ## Support of a decoration in its apex -/

/-- Wires consumed by a decoration lie in its apex. -/
theorem HDec.consumed_mem_apex {X Y : Finset Wire} {m : AlignedLoose X Y}
    (T : HDec ty m) : ∀ w ∈ consumedW T.1, w ∈ m.apex := by
  intro w hw
  obtain ⟨a, ha, hwa⟩ := mem_consumedW.mp hw
  exact T.2.2 a ha w (List.mem_append_left _ hwa)

/-- Wires produced by a decoration lie in its apex. -/
theorem HDec.produced_mem_apex {X Y : Finset Wire} {m : AlignedLoose X Y}
    (T : HDec ty m) : ∀ w ∈ producedW T.1, w ∈ m.apex := by
  intro w hw
  obtain ⟨a, ha, hwa⟩ := mem_producedW.mp hw
  exact T.2.2 a ha w (List.mem_append_right _ hwa)

/-! ## The adapter to open hypernets -/

/-- A well-formed decorated loose arrow, packaged as an open hypernet:
the wire typing is the ambient table restricted to the apex, the
interfaces are the feet's element lists, and every well-formedness
field is one of the clauses. -/
noncomputable def IsWf.toOpen {X Y : Finset Wire} {m : AlignedLoose X Y}
    (T : HDec ty m) (h : IsWf X Y T.1) : OpenHypernet where
  net :=
    { wireType := tableOn ty m.apex
      applications := T.1
      linearity := h.linear
      acyclic := h.ssa
      typeConsistent := T.2.1 }
  inputs := X.toList
  outputs := Y.toList
  inputs_nodup := X.nodup_toList
  outputs_nodup := Y.nodup_toList
  inputs_unproduced := fun w hw =>
    h.inputs_unproduced w (Finset.mem_toList.mp hw)
  consumed_covered := fun w hw hnp =>
    Finset.mem_toList.mpr (h.consumed_covered w hw hnp)
  outputs_unconsumed := fun w hw =>
    h.outputs_unconsumed w (Finset.mem_toList.mp hw)
  outputs_grounded := fun w hw =>
    (h.outputs_grounded w (Finset.mem_toList.mp hw)).imp id
      Finset.mem_toList.mpr

section ToOpen

variable {X Y : Finset Wire} {m : AlignedLoose X Y}

@[simp] theorem toOpen_net_applications (T : HDec ty m) (h : IsWf X Y T.1) :
    (h.toOpen ty T).net.applications = T.1 := rfl

@[simp] theorem toOpen_net_wireType (T : HDec ty m) (h : IsWf X Y T.1) :
    (h.toOpen ty T).net.wireType = tableOn ty m.apex := rfl

@[simp] theorem toOpen_inputs (T : HDec ty m) (h : IsWf X Y T.1) :
    (h.toOpen ty T).inputs = X.toList := rfl

@[simp] theorem toOpen_outputs (T : HDec ty m) (h : IsWf X Y T.1) :
    (h.toOpen ty T).outputs = Y.toList := rfl

/-- Every wire the packaged open hypernet touches lies in the apex:
diagram support is the decoration's bundle, interfaces are the feet. -/
theorem toOpen_wires_mem_apex (T : HDec ty m) (h : IsWf X Y T.1) :
    ∀ w ∈ (h.toOpen ty T).wires, w ∈ m.apex := by
  intro w hw
  unfold OpenHypernet.wires at hw
  rcases List.mem_append.mp hw with hw | hw
  · rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · exact HDec.consumed_mem_apex ty T w hw
      · exact HDec.produced_mem_apex ty T w hw
    · exact m.left_le (Finset.mem_toList.mp hw)
  · exact m.right_le (Finset.mem_toList.mp hw)

end ToOpen

/-! ## Units are well-formed -/

/-- The empty diagram between equal feet is well-formed: the loose
identities of the double category of open hypernets lie in the
fragment. -/
theorem isWf_unit (X : Finset Wire) : IsWf X X [] where
  linear := ⟨List.nodup_nil, List.nodup_nil⟩
  ssa := fun i => i.elim0
  inputs_unproduced := fun _ _ h => nomatch h
  consumed_covered := fun _ hw _ => nomatch hw
  outputs_unconsumed := fun _ _ h => nomatch h
  outputs_grounded := fun _ hw => Or.inr hw

/-! ## Composition: the aligned-gluing hypotheses on the locus -/

/-- On the seam-disjoint locus, the packaged open hypernets of two
composable well-formed decorated looses satisfy the aligned-gluing
hypotheses: the seam is literal name sharing, typing compatibility is
automatic (both typings restrict the one ambient table), and the
wire-sharing bound is the locus condition read through the apexes. -/
theorem toOpen_aligned {X Y Z : Finset Wire} {m : AlignedLoose X Y}
    {n : AlignedLoose Y Z} (T₁ : HDec ty m) (T₂ : HDec ty n)
    (h₁ : IsWf X Y T₁.1) (h₂ : IsWf Y Z T₂.1)
    (hdisj : ∀ w ∈ m.apex, w ∈ n.apex → w ∈ Y) :
    OpenHypernet.Aligned (h₁.toOpen ty T₁) (h₂.toOpen ty T₂) where
  seam := rfl
  compat := fun w τ τ' hm hn => by
    have h1 : ty w = some τ :=
      (tableOn_pos ty (mem_of_tableOn_some ty hm)).symm.trans hm
    have h2 : ty w = some τ' :=
      (tableOn_pos ty (mem_of_tableOn_some ty hn)).symm.trans hn
    exact Option.some.inj (h1.symm.trans h2)
  disj := fun w hwH hwG =>
    Finset.mem_toList.mpr
      (hdisj w (toOpen_wires_mem_apex ty T₁ h₁ w hwH)
        (toOpen_wires_mem_apex ty T₂ h₂ w hwG))

/-- **The fragment is closed under loose composition on the
seam-disjoint locus**: the concatenation of two well-formed diagrams
across a shared boundary is well-formed.  Every clause is a field of
the landed gluing theorem `PPLC.OpenHypernet.glue`, pulled back through
the adapter — the seam combinatorics are not re-proved. -/
theorem IsWf.glue {X Y Z : Finset Wire} {m : AlignedLoose X Y}
    {n : AlignedLoose Y Z} {T₁ : HDec ty m} {T₂ : HDec ty n}
    (h₁ : IsWf X Y T₁.1) (h₂ : IsWf Y Z T₂.1)
    (hdisj : ∀ w ∈ m.apex, w ∈ n.apex → w ∈ Y) :
    IsWf X Z (T₁.1 ++ T₂.1) :=
  have hA := toOpen_aligned ty T₁ T₂ h₁ h₂ hdisj
  { linear := (OpenHypernet.glue hA).net.linearity
    ssa := (OpenHypernet.glue hA).net.acyclic
    inputs_unproduced := fun w hw =>
      (OpenHypernet.glue hA).inputs_unproduced w (Finset.mem_toList.mpr hw)
    consumed_covered := fun w hw hnp =>
      Finset.mem_toList.mp
        ((OpenHypernet.glue hA).consumed_covered w hw hnp)
    outputs_unconsumed := fun w hw =>
      (OpenHypernet.glue hA).outputs_unconsumed w (Finset.mem_toList.mpr hw)
    outputs_grounded := fun w hw =>
      ((OpenHypernet.glue hA).outputs_grounded w
        (Finset.mem_toList.mpr hw)).imp id Finset.mem_toList.mp }

/-! ## The adapter intertwines composition and units -/

/-- The adapter sends loose composition to gluing, on the nose: the
packaged open hypernet of a glued decoration is the glued packaged open
hypernet.  The typing leg is the union/merge exchange of restricted
ambient tables. -/
theorem toOpen_glue {X Y Z : Finset Wire} {m : AlignedLoose X Y}
    {n : AlignedLoose Y Z} (T₁ : HDec ty m) (T₂ : HDec ty n)
    (h₁ : IsWf X Y T₁.1) (h₂ : IsWf Y Z T₂.1)
    (hdisj : ∀ w ∈ m.apex, w ∈ n.apex → w ∈ Y) :
    (h₁.glue ty h₂ hdisj).toOpen ty (HDec.glue ty T₁ T₂)
      = OpenHypernet.glue (toOpen_aligned ty T₁ T₂ h₁ h₂ hdisj) := by
  refine OpenHypernet.ext' ?_ rfl rfl
  refine Hypernet.ext' ?_ rfl
  exact (mergeWt_tableOn ty m.apex n.apex).symm

/-- The adapter sends the unit decoration to the loose identity of the
open-hypernet composition layer, on the nose. -/
theorem toOpen_unit (X : Finset Wire) :
    (isWf_unit X).toOpen ty (HDec.empty ty X)
      = OpenHypernet.unitOpen X.toList (tableOn ty X) X.nodup_toList :=
  rfl

/-! ## The fragment at the level of the double category -/

/-- Well-formedness of a loose arrow of the double category of open
hypernets: its decoration satisfies the clauses between its feet.  The
well-formed loose arrows, with all cells between them, are the
sub-double-category of the hypernets of the certificate calculus,
composable on the seam-disjoint locus. -/
abbrev IsWfLoose {p q : HNet ty} (M : SpanValued.GLoose p q) : Prop :=
  IsWf p.1.roster q.1.roster M.dec.1

/-- The loose identities of the double category of open hypernets are
well-formed. -/
theorem isWfLoose_id (p : HNet ty) :
    IsWfLoose ty (SpanValued.GLoose.id p) :=
  isWf_unit p.1.roster

/-- Well-formedness of loose arrows is preserved by loose composition
on the seam-disjoint locus. -/
theorem IsWfLoose.comp {p q r : HNet ty} {M : SpanValued.GLoose p q}
    {N : SpanValued.GLoose q r} (hM : IsWfLoose ty M) (hN : IsWfLoose ty N)
    (hdisj : ∀ w ∈ M.base.apex, w ∈ N.base.apex → w ∈ q.1.roster) :
    IsWfLoose ty (SpanValued.GLoose.comp M N) :=
  IsWf.glue ty (T₁ := M.dec) (T₂ := N.dec) hM hN hdisj

end SuFunctor

#print axioms SuFunctor.HDec.consumed_mem_apex
#print axioms SuFunctor.HDec.produced_mem_apex
#print axioms SuFunctor.IsWf.toOpen
#print axioms SuFunctor.toOpen_wires_mem_apex
#print axioms SuFunctor.isWf_unit
#print axioms SuFunctor.toOpen_aligned
#print axioms SuFunctor.IsWf.glue
#print axioms SuFunctor.toOpen_glue
#print axioms SuFunctor.toOpen_unit
#print axioms SuFunctor.isWfLoose_id
#print axioms SuFunctor.IsWfLoose.comp
