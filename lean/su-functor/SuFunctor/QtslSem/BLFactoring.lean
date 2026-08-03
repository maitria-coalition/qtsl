import SuFunctor.QtslSem.Fixture
import SuFunctor.QtslSem.SpecJudg
import DoubleCat.Vert

/-!
# The structural fragment factored through the judgment layer

The demonstration the carrier design owes: the scaffold's BL
interpretation re-targeted from the implication double category to the
judgment layer (`DoubleCat.JudgLayer`) at the propositional datum over
the vertically-trivial base — and the acceptance fixture re-run through
the promoted functor into the new carrier, landing at the same
checker-face statement.

The components are the **same landed soundness lemmas, unchanged**:
each arm below is the corresponding arm of
`SuFunctor.QtslSem.blInterpretation` with the judgment layer's
existence-witness (the trivial base cell) adjoined — the mechanical
adaptation, and nothing else.  The fixture twin reuses the scaffold's
`cutCovering` verbatim (it lives in the free promotion of the presented
source, which is target-independent), so the two routes differ only in
the carrier — which is the point.
-/

namespace SuFunctor

namespace QtslSem

open PPLC CategoryTheory VdcPresentation
open VirtualDoubleCategoryData

/-- The propositional judgment layer over the trivial double reading of
the claim context: the scaffold's `ImplDouble BLCtx`, as the judgment
layer's Prop-shadow. -/
abbrev BLJudg : Type :=
  JudgLayer (Vert BLCtx) (JudgmentOrder.propDatum)

/-- The tight functor of the re-targeted interpretation: wrap twice. -/
def blTightJ : BLCtx ⥤ BLJudg where
  obj x := ⟨⟨x⟩⟩
  map f := f

/-- **The fold lemma for the list builder, at the judgment layer**: the
decoration of the interpreted fold of a list-built premise string is
the validity of every component (the propositional datum's lax
composition is conjunction with `True` as unit — the decoration fold
mirrors the implication carrier). -/
theorem foldJ_ofList_valid (H : Hypernet) :
    ∀ (l : List Sequent),
    (((LoosePath.ofList (a := BLCtx.pt)
        (L := fun _ _ : BLCtx => Sequent) l).map blTightJ.obj
      (fun {a b} seq =>
        (⟨⟨⟩, seq.semanticallyValid H⟩ :
          PseudoDoubleCategoryStruct.Loose (blTightJ.obj a)
            (blTightJ.obj b)))).fold).dec ↔
      ∀ c ∈ l, c.semanticallyValid H
  | [] => ⟨fun _ c hc => (nomatch hc), fun _ => trivial⟩
  | c :: t => by
      rw [List.forall_mem_cons]
      exact and_congr Iff.rfl (foldJ_ofList_valid H t)

/-- **The fold lemma for the family builder, at the judgment layer**:
the decoration of the interpreted fold of a `Fin`-built premise string
is the validity of every branch. -/
theorem foldJ_ofFin_valid (H : Hypernet) :
    ∀ {n : Nat} (f : Fin n → Sequent),
    (((LoosePath.ofFin (a := BLCtx.pt)
        (L := fun _ _ : BLCtx => Sequent) f).map blTightJ.obj
      (fun {a b} seq =>
        (⟨⟨⟩, seq.semanticallyValid H⟩ :
          PseudoDoubleCategoryStruct.Loose (blTightJ.obj a)
            (blTightJ.obj b)))).fold).dec ↔
      ∀ k, (f k).semanticallyValid H
  | 0, _ => ⟨fun _ k => k.elim0, fun _ => trivial⟩
  | n + 1, f => by
      rw [Fin.forall_fin_succ]
      exact and_congr Iff.rfl (foldJ_ofFin_valid H fun k => f k.succ)

/-- **The wired fragment interpreted in the judgment layer**: a
sequent is read as its semantic validity over `H` (the decoration of
the trivial loose arrow), and each rule generator's component is its
landed soundness lemma — the same lemma application as in
`blInterpretation`, with the trivial base-cell witness adjoined. -/
def blInterpretationJ (H : Hypernet) :
    VdcInterpretation (blPresentation H) BLJudg where
  tight := blTightJ
  interpLoose := fun seq => ⟨⟨⟩, seq.semanticallyValid H⟩
  component := fun r hr =>
    match r, hr with
    | .ax _, h => by exact ⟨⟨⟨⟩, fun _ => sound_ax h⟩⟩
    | .weaken _ _ _, ⟨h₁, h₂⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_weaken hs.1 h₁ h₂⟩⟩
    | .cut _ _ _ _, ⟨h₁, h₂, h₃, h₄⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_cut hs.1 hs.2.1 h₁ h₂ h₃ h₄⟩⟩
    | .andI _ _ _, ⟨h₁, h₂, h₃⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_andI hs.1 hs.2.1 h₁ h₂ h₃⟩⟩
    | .andELeft _ _ _, ⟨h₁, h₂⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_andE_left hs.1 h₁ h₂⟩⟩
    | .andERight _ _ _, ⟨h₁, h₂⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_andE_right hs.1 h₁ h₂⟩⟩
    | .orILeft _ _ _, ⟨h₁, h₂⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_orI_left hs.1 h₁ h₂⟩⟩
    | .orIRight _ _ _, ⟨h₁, h₂⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_orI_right hs.1 h₁ h₂⟩⟩
    | .orE _ _ _, ⟨h₁, h₂, h₃⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_orE hs.1 hs.2.1 h₁ h₂ h₃⟩⟩
    | .eqRefl _ _, ⟨h₁, h₂, h₃⟩ => by
        exact ⟨⟨⟨⟩, fun _ => sound_eqRefl h₁ h₂ h₃⟩⟩
    | .eqSym _ _ _ _, ⟨h₁, h₂, h₃⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_eqSym hs.1 h₁ h₂ h₃⟩⟩
    | .antisym _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_antisym hs.1 hs.2.1 h₁ h₂ h₃ h₄ h₅⟩⟩
    | .eqElim _ _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_eqElim hs.1 hs.2.1 h₁ h₂ h₃ h₄ h₅ h₆⟩⟩
    | .arithAtomFold _ _ _ _ _, ⟨h₁, h₂, h₃⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_arithAtom_fold hs.1 h₁ h₂ h₃⟩⟩
    | .arithAtomUnfold _ _ _ _ _, ⟨h₁, h₂, h₃⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_arithAtom_unfold hs.1 h₁ h₂ h₃⟩⟩
    | .norm _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨⟨⟨⟩, fun _ => sound_norm h₁ h₂ h₃ h₄ h₅ h₆⟩⟩
    | .farkas _ _ _, ⟨h₁, h₂, h₃, h₄, h₅⟩ => by
        exact ⟨⟨⟨⟩, fun _ => sound_farkas h₁ h₂ h₃ h₄ h₅⟩⟩
    | .pConstExact _ _ _ _, ⟨h₁, h₂⟩ => by
        exact ⟨⟨⟨⟩, fun _ => sound_pConstExact h₁ h₂⟩⟩
    | .convIntro _ _ _ _ _, ⟨h₁, h₂, h₃, h₄⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_convIntro hs.1 h₁ h₂ h₃ h₄⟩⟩
    | .convElim _ _ _ _ _, ⟨h₁, h₂, h₃⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_convElim hs.1 h₁ h₂ h₃⟩⟩
    | .bernConeEmpty _ _ _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => by
        exact ⟨⟨⟨⟩, fun hs =>
          sound_bernCone_empty hs.1 h₁ h₂ h₃ h₄ h₅ h₆ h₇⟩⟩
    | .bernCone _ _ _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_bernCone hs.1 h₁ h₂ h₃ h₄ h₅ h₆⟩⟩
    | .promise seq supplier consumer contract path iface ctx,
        ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_promise
          ⟨seq, supplier, consumer, contract, path, iface, ctx,
            h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ hs.1 hs.2.1⟩⟩
    | .psdCertOf _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨⟨⟨⟩, fun _ => sound_psdCertOf h₁ h₂ h₃ h₄ h₅ h₆⟩⟩
    | .psdCertT _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨⟨⟨⟩, fun _ => sound_psdCertT h₁ h₂ h₃ h₄ h₅ h₆⟩⟩
    | .psdCertDD _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨⟨⟨⟩, fun _ => sound_psdCertDD h₁ h₂ h₃ h₄ h₅ h₆⟩⟩
    | .psdCertK _ _ _ _ _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨⟨⟨⟩, fun _ => sound_psdCertK h₁ h₂ h₃ h₄ h₅ h₆⟩⟩
    | .reluNN _ _ _, ⟨h₁, h₂⟩ => by
        exact ⟨⟨⟨⟩, fun _ => sound_reluNN h₁ h₂⟩⟩
    | .reluAbove _ _ _, ⟨h₁, h₂⟩ => by
        exact ⟨⟨⟨⟩, fun _ => sound_reluAbove h₁ h₂⟩⟩
    | .reluPos _ _ _ _, ⟨h₁, h₂, h₃, h₄⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_reluPos hs.1 h₁ h₂ h₃ h₄⟩⟩
    | .reluNeg _ _ _ _, ⟨h₁, h₂, h₃, h₄⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_reluNeg hs.1 h₁ h₂ h₃ h₄⟩⟩
    | .reluSplit _ _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => by
        exact ⟨⟨⟨⟩, fun hs =>
          sound_reluSplit hs.1 hs.2.1 h₁ h₂ h₃ h₄ h₅ h₆ h₇⟩⟩
    | .lirpa _ _ _ _ _ _ _ _ _ _ _,
        ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_lirpa hs.1 hs.2.1 h₁ h₂ h₃ h₄ h₅ h₆
          h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄⟩⟩
    | .cellInInterior _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_cellInInterior hs.1 h₁ h₂ h₃ h₄ h₅ h₆⟩⟩
    | .cellOut _ _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_cellOut hs.1 h₁ h₂ h₃ h₄ h₅ h₆⟩⟩
    | .subdivide _ _ _ branchPremise _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_subdivide hs.1
          ((foldJ_ofFin_valid H branchPremise).mp hs.2) h₁ h₂ h₃ h₄ h₅⟩⟩
    | .pBound _ components _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_pBound
          ((foldJ_ofList_valid H components).mp hs) h₁ h₂ h₃ h₄ h₅ h₆ h₇⟩⟩
    | .syzygy seq components combination conclusion,
        ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => by
        exact ⟨⟨⟨⟩, fun hs => sound_syzygy
          ⟨seq, components, combination, conclusion,
            h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
          ((foldJ_ofList_valid H components).mp hs)⟩⟩

/-- The semantics off the presentation, into the judgment layer: the
free-promotion transpose, with the thin-target hypothesis discharged by
the judgment layer's own thinness theorem — the eligibility the
carrier design owes, exercised. -/
noncomputable def qtslSemBLJ (H : Hypernet) :
    LaxDoubleFunctor (FreePromotion (Presented (blPresentation H)))
      BLJudg :=
  (blInterpretationJ H).sem fun m n f g =>
    JudgLayer.cell_subsingleton m n f g

/-- **The fixture twin: cut, composed through the universal property
into the judgment layer, lands at the same checker face.**  Hypotheses
and endpoint are the scaffold fixture's, verbatim; the proof term
routes through the promoted functor into the new carrier, on the
scaffold's own covering cell. -/
theorem cut_face_through_promotionJ (H : Hypernet) (φ χ ψ : Formula)
    (h₁ : Sequent.semanticallyValid H ⟨φ, χ⟩)
    (h₂ : Sequent.semanticallyValid H ⟨.and φ χ, ψ⟩) :
    Plain.upperProb (Plain.admCyl H ⟨φ, ψ⟩) (Plain.postEvt H ⟨φ, ψ⟩)ᶜ = 0 := by
  obtain ⟨_, himp⟩ := ((qtslSemBLJ H).mapCell (cutCovering H φ χ ψ)).down
  exact (Plain.semanticallyValid_iff_face H ⟨φ, ψ⟩).mp
    (himp ⟨h₁, h₂, trivial⟩).1

/-- **The tranche fixture's twin: the composite `eqElim`/`pConstExact`
derivation, composed through the universal property into the judgment
layer, lands at the same checker face.**  Hypotheses and endpoint are
the tranche fixture's, verbatim; the proof term routes through the
promoted functor into the carrier, on the same composite covering
cell. -/
theorem eqElim_const_face_through_promotionJ (H : Hypernet) (φ : Formula)
    (h : Sequent.semanticallyValid H
      ⟨φ, .atom .le (.add (.const 2) (.const 4)) (.const 10)⟩) :
    Plain.upperProb (Plain.admCyl H ⟨φ, .atom .le (.const 6) (.const 10)⟩)
      (Plain.postEvt H ⟨φ, .atom .le (.const 6) (.const 10)⟩)ᶜ = 0 := by
  obtain ⟨_, himp⟩ :=
    ((qtslSemBLJ H).mapCell (eqElimConstCovering H φ)).down
  exact (Plain.semanticallyValid_iff_face H (constConcl φ)).mp
    (himp ⟨h, trivial⟩).1

/-- **The relu-chain fixture's twin: the premise-free composite,
composed through the universal property into the judgment layer, lands
at the same checker face.**  Hypotheses and endpoint are the relu-chain
fixture's, verbatim; the proof term routes through the promoted functor
into the carrier, on the same composite covering cell. -/
theorem reluChain_face_through_promotionJ (H : Hypernet) (φ : Formula)
    (u v w : Wire) (h₁ : reluLinked H u v) (h₂ : reluLinked H v w) :
    Plain.upperProb (Plain.admCyl H ⟨φ, .atom .eq (.var w) (.var v)⟩)
      (Plain.postEvt H ⟨φ, .atom .eq (.var w) (.var v)⟩)ᶜ = 0 := by
  obtain ⟨_, himp⟩ :=
    ((qtslSemBLJ H).mapCell (reluChainCovering H φ u v w h₁ h₂)).down
  exact (Plain.semanticallyValid_iff_face H (reluChainConcl φ v w)).mp
    (himp trivial).1

/-- **The fan fixture's twin: the `Fin`-built composite, composed
through the universal property into the judgment layer, lands at the
same checker face.**  Hypotheses and endpoint are the fan fixture's,
verbatim; the proof term routes through the promoted functor into the
carrier, on the same composite covering cell. -/
theorem subdivideFan_face_through_promotionJ (H : Hypernet)
    (φ ψ hpF : Formula) (termX : Term) (simplex : Simplex)
    (S : ExtensionSet) (branchSimplex : Fin 2 → Simplex)
    (branchS : Fin 2 → ExtensionSet) (cert : Term)
    (hbshape : termX.bshape H = some [simplex.complex.ambDim])
    (hform : barycentricHalfspaceForm termX simplex S hpF)
    (hcover : coverInfeasibilityValid termX simplex S 2
      branchSimplex branchS cert)
    (h₁ : Sequent.semanticallyValid H ⟨φ, hpF⟩)
    (h₂ : Sequent.semanticallyValid H
      ⟨.and φ (.inRegion termX (branchSimplex 0) (branchS 0)), ψ⟩)
    (h₃ : Sequent.semanticallyValid H
      ⟨.and φ (.inRegion termX (branchSimplex 1) (branchS 1)), ψ⟩) :
    Plain.upperProb (Plain.admCyl H ⟨φ, ψ⟩) (Plain.postEvt H ⟨φ, ψ⟩)ᶜ = 0 := by
  obtain ⟨_, himp⟩ := ((qtslSemBLJ H).mapCell
    (subdivideFanCovering H φ ψ hpF termX simplex S branchSimplex
      branchS cert hbshape hform hcover)).down
  exact (Plain.semanticallyValid_iff_face H ⟨φ, ψ⟩).mp
    (himp ⟨h₁, h₂, h₃, trivial⟩).1

/-- **The pair fixture's twin: the list-built bare generator, composed
through the universal property into the judgment layer, lands at the
same checker face.**  Hypotheses and endpoint are the pair fixture's,
verbatim; the proof term routes through the promoted functor into the
carrier, on the same covering cell. -/
theorem syzygyPair_face_through_promotionJ (H : Hypernet)
    (seq c₁ c₂ : Sequent) (combination conclusion : Term)
    (hpreC : ∀ c ∈ [c₁, c₂], premiseContains seq.pre c.pre)
    (hshape : ∃ s, conclusion.bshape H = some s)
    (hfin : conclusion.finWires H)
    (hwpos : ∀ w ∈ seq.pre.freeWires ++ conclusion.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
    (hcompPos : ∀ c ∈ [c₁, c₂], ∀ w ∈ c.post.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
    (hvalid : syzygyCombinationValid combination [c₁, c₂] seq.pre
      conclusion)
    (hform : syzygyConclusionForm conclusion seq.post)
    (hv₁ : c₁.semanticallyValid H) (hv₂ : c₂.semanticallyValid H) :
    Plain.upperProb (Plain.admCyl H seq) (Plain.postEvt H seq)ᶜ = 0 := by
  obtain ⟨_, himp⟩ := ((qtslSemBLJ H).mapCell
    (syzygyPairCovering H seq c₁ c₂ combination conclusion hpreC hshape
      hfin hwpos hcompPos hvalid hform)).down
  exact (Plain.semanticallyValid_iff_face H seq).mp
    (himp ⟨hv₁, hv₂, trivial⟩).1

/-- **The antisym fixture's twin: the fully-discharged two-premise
composite, composed through the universal property into the judgment
layer, lands at the same checker face.**  Hypotheses and endpoint are
the antisym fixture's, verbatim; the proof term routes through the
promoted functor into the carrier, on the same composite covering
cell. -/
theorem antisymConst_face_through_promotionJ (H : Hypernet)
    (φ : Formula) :
    Plain.upperProb
      (Plain.admCyl H ⟨φ, .atom .eq (.add (.const 2) (.const 4)) (.const 6)⟩)
      (Plain.postEvt H
        ⟨φ, .atom .eq (.add (.const 2) (.const 4)) (.const 6)⟩)ᶜ = 0 := by
  obtain ⟨_, himp⟩ :=
    ((qtslSemBLJ H).mapCell (antisymConstCovering H φ)).down
  exact (Plain.semanticallyValid_iff_face H (antisymConcl φ)).mp
    (himp trivial).1

end QtslSem

end SuFunctor
