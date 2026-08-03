import SuFunctor.QtslSem.BLFactoring
import Qtsl.ProductLattice

/-!
# The many-object presentation: hypernet contexts, extension tights,
# and the product-lattice rule

The first presentation instance with many objects and nonidentity tight
arrows — the shape `DoubleCat.Virtual.Presentation` was built to carry
("rules along nonidentity tight arrows (transport along a simulation,
composition along a wiring) need the double reading") and the shape the
single-context presentation's claim context could not: the
product-lattice rule (`Qtsl.ProductLattice`) has premise validities
over factor hypernets and a conclusion over their disjoint union, so it
is inter-context transport, not sequent calculus over one context.

**The context category** `BLHCtx` has hypernets as objects and
extension witnesses as tight arrows: `H ⟶ H'` is the pair of a
wire-type extension and an application inclusion — exactly the two
transport hypotheses of `Sequent.semanticallyValid_extend`, which is
why they live in the arrow rather than in a gate: the presentation's
frame functions are total, so the conditions that make the frame an
arrow are arrow data, and the rule's remaining hypothesis
(`wellScoped`, a condition on the sequent, not on the arrow) is the
gate.  All three hypotheses appear verbatim in the component's
application of the lemma.

**The rules** are the single-context roster, embedded (`emb` — each
rule of `blPresentation H` resides at context `⟨H⟩` with identity tight
sides; the single-context presentation is the one-context slice of this
one), plus one new primitive generator: `extend` — the same sequent,
transported along an extension arrow, framed by that arrow on both
tight sides.  Its component is `Sequent.semanticallyValid_extend`.  The
embedded components are **reused, not re-derived**: the fold-transport
lemmas (`fold_emb_valid`, `foldJ_emb_valid`) identify the interpreted
premise folds, and each embedded arm applies the single-context
component across that identification.

**The product-lattice rule is derived, not a generator.**  The cite
step (`citeFacet`) is extend-then-weaken — `citeDeriv` splices the
`extend` generator into the already-wired weakening by simultaneous
substitution, giving the first covering in this development whose tight
sides are nonidentity — and the batch lemma is a fold of cite cells
over the product blocks (`sound_productLattice_through_M`, recovering
the statement of `sound_productLattice` with every facet's validity
routed through the promoted functor).  The rider of a cite facet is a
free parameter (the join-context, weakened in): the rule holds for
every rider, so no side condition pins it.

Where the single-context story mints one semantics per hypernet
(`qtslSemBL H`), the many-object story mints **one functor**
(`qtslSemBLM`) whose source carries all hypernets and their extension
arrows at once.
-/

namespace SuFunctor

namespace QtslSem

open PPLC CategoryTheory VdcPresentation
open VirtualDoubleCategoryData

/-- A claim context of the many-object presentation: a hypernet,
wrapped so the context category collides with nothing the hypernet
type itself carries. -/
structure BLHCtx : Type where
  /-- Wrap a hypernet as a context. -/
  of ::
  /-- The hypernet. -/
  ctx : Hypernet

/-- A tight arrow of the context category: an extension witness — the
wire-type extension together with the application inclusion.  These are
exactly the two transport hypotheses of
`Sequent.semanticallyValid_extend`; the arrow is the pair. -/
structure BLHExt (a b : BLHCtx) : Type where
  /-- Every wire typed in the source is typed identically in the
  target. -/
  wireExtends : a.ctx.WireExtends b.ctx
  /-- Every application row of the source is an application row of the
  target. -/
  appsIncluded : ∀ app ∈ a.ctx.applications, app ∈ b.ctx.applications

instance BLHExt.instSubsingleton {a b : BLHCtx} :
    Subsingleton (BLHExt a b) :=
  ⟨fun x y => by cases x; cases y; rfl⟩

/-- The context category is thin: the extension relation, as a
category.  Identity and composition are field-wise; the laws are proof
irrelevance. -/
instance : Category.{0} BLHCtx where
  Hom := BLHExt
  id _ := ⟨fun _ _ h => h, fun _ h => h⟩
  comp f g :=
    ⟨fun w τ h => g.wireExtends w τ (f.wireExtends w τ h),
     fun app h => g.appsIncluded app (f.appsIncluded app h)⟩
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

/-- The rule instances of the many-object presentation: the embedded
single-context roster, and the extend-transport generator. -/
inductive BLMRule : Type
  /-- A rule of the single-context presentation, residing at context
  `⟨H⟩` with identity tight sides. -/
  | emb (H : Hypernet) (r : BLRule)
  /-- Extend-transport: the sequent `seq`, transported from context `a`
  to context `b` along the extension arrow `e`, which frames both tight
  sides. -/
  | extend (a b : BLHCtx) (e : BLHExt a b) (seq : Sequent)

namespace BLMRule

/-- The side conditions: an embedded rule keeps its own gate at its
context; extend-transport requires the sequent well-scoped over the
source (the third hypothesis of `Sequent.semanticallyValid_extend` —
the other two are the arrow's fields). -/
def gate : BLMRule → Prop
  | .emb H r => r.gate H
  | .extend a _ _ seq => seq.wellScoped a.ctx

/-- The source corner of a rule's frame (top-left and top-right
coincide for both constructors). -/
def src : BLMRule → BLHCtx
  | .emb H _ => ⟨H⟩
  | .extend a _ _ _ => a

/-- The target corner of a rule's frame (bottom-left and bottom-right
coincide for both constructors). -/
def tgt : BLMRule → BLHCtx
  | .emb H _ => ⟨H⟩
  | .extend _ b _ _ => b

/-- The tight side of a rule's multicell (left and right coincide):
identity for embedded rules, the extension arrow for
extend-transport. -/
def arrow : (r : BLMRule) → (r.src ⟶ r.tgt)
  | .emb H _ => 𝟙 (BLHCtx.of H)
  | .extend _ _ e _ => e

/-- The premise string: the embedded rule's own string, re-homed at its
context; a single premise for extend-transport. -/
def tops : (r : BLMRule) →
    LoosePath (fun _ _ : BLHCtx => Sequent) r.src r.src
  | .emb H r => (BLRule.tops r).map (fun _ => BLHCtx.of H) (fun {_ _} e => e)
  | .extend _ _ _ seq => .single seq

/-- The conclusion: the embedded rule's own, or the transported
sequent. -/
def concl : BLMRule → Sequent
  | .emb _ r => r.concl
  | .extend _ _ _ seq => seq

end BLMRule

/-- **The many-object presentation**: sequents as loose generators over
hypernet contexts, the embedded single-context roster plus the
extend-transport generator as gated multicell generators — the first
presentation in this development with many objects and nonidentity
tight arrows. -/
def blPresentationM : VdcPresentation BLHCtx where
  Loose _ _ := Sequent
  Rule := BLMRule
  gate := BLMRule.gate
  srcL := BLMRule.src
  srcR := BLMRule.src
  tgtL := BLMRule.tgt
  tgtR := BLMRule.tgt
  tops := BLMRule.tops
  bot := BLMRule.concl
  left := BLMRule.arrow
  right := BLMRule.arrow

/-- The tight functor of the interpretation: the wrapping bijection on
contexts. -/
def blMTight : BLHCtx ⥤ ImplDouble BLHCtx where
  obj x := ⟨x⟩
  map f := f

/-- The propositional judgment layer over the trivial double reading of
the context category: the many-object sibling of `BLJudg`. -/
abbrev BLJudgM : Type :=
  JudgLayer (Vert BLHCtx) (JudgmentOrder.propDatum)

/-- The tight functor of the judgment-layer interpretation: wrap
twice. -/
def blMTightJ : BLHCtx ⥤ BLJudgM where
  obj x := ⟨⟨x⟩⟩
  map f := f

/-- **The fold-transport lemma, implication carrier**: interpreting an
embedded premise string in the many-object carrier folds to the same
proposition as interpreting the original string in the single-context
carrier — every endpoint of an embedded string is `⟨H⟩`, so the
source-context reading agrees conjunct by conjunct.  This is the
component-reuse device: the embedded arms of the interpretation apply
the single-context components across this identification, so the roster
is wired once, not twice. -/
theorem fold_emb_valid (H : Hypernet) :
    ∀ {a b : BLCtx} (ps : LoosePath (fun _ _ : BLCtx => Sequent) a b),
    (((ps.map (M := fun _ _ : BLHCtx => Sequent) (fun _ => BLHCtx.of H)
        (fun {_ _} e => e)).map blMTight.obj
        (fun {x y} (seq : Sequent) => (seq.semanticallyValid x.ctx :
          PseudoDoubleCategoryStruct.Loose (blMTight.obj x)
            (blMTight.obj y)))).fold ↔
      ((ps.map blTight.obj
        (fun {_ _} seq => seq.semanticallyValid H)).fold))
  | _, _, .nil => Iff.rfl
  | _, _, .cons _ p => and_congr Iff.rfl (fold_emb_valid H p)

/-- **The fold-transport lemma, judgment layer**: the decoration of the
interpreted fold of an embedded premise string agrees with the
single-context reading. -/
theorem foldJ_emb_valid (H : Hypernet) :
    ∀ {a b : BLCtx} (ps : LoosePath (fun _ _ : BLCtx => Sequent) a b),
    ((((ps.map (M := fun _ _ : BLHCtx => Sequent) (fun _ => BLHCtx.of H)
        (fun {_ _} e => e)).map blMTightJ.obj
        (fun {x y} (seq : Sequent) => (⟨⟨⟩, seq.semanticallyValid x.ctx⟩ :
          PseudoDoubleCategoryStruct.Loose (blMTightJ.obj x)
            (blMTightJ.obj y)))).fold).dec ↔
      (((ps.map blTightJ.obj
        (fun {a b} seq => (⟨⟨⟩, seq.semanticallyValid H⟩ :
          PseudoDoubleCategoryStruct.Loose (blTightJ.obj a)
            (blTightJ.obj b)))).fold).dec))
  | _, _, .nil => Iff.rfl
  | _, _, .cons _ p => and_congr Iff.rfl (foldJ_emb_valid H p)

/-- **The interpretation of the many-object presentation**: a sequent
at context `x` is read as its semantic validity over `x`'s hypernet;
each embedded rule's component is the single-context component, reused
across the fold-transport identification; the extend-transport
component is `Sequent.semanticallyValid_extend`, its three hypotheses
supplied verbatim — two from the arrow, one from the gate. -/
def blMInterpretation :
    VdcInterpretation blPresentationM (ImplDouble BLHCtx) where
  tight := blMTight
  interpLoose := fun {x _} seq => seq.semanticallyValid x.ctx
  component := fun r hr =>
    match r, hr with
    | .emb H r', hr' => by
        exact ⟨fun hs => ((blInterpretation H).component r' hr').down
          ((fold_emb_valid H (BLRule.tops r')).mp hs)⟩
    | .extend _ _ e _, hws => by
        exact ⟨fun hs => Sequent.semanticallyValid_extend
          e.wireExtends e.appsIncluded hws hs.1⟩

/-- **The judgment-layer interpretation of the many-object
presentation**: the same two arms, with the trivial base-cell witness
adjoined. -/
def blMInterpretationJ :
    VdcInterpretation blPresentationM BLJudgM where
  tight := blMTightJ
  interpLoose := fun {x _} seq => ⟨⟨⟩, seq.semanticallyValid x.ctx⟩
  component := fun r hr =>
    match r, hr with
    | .emb H r', hr' => by
        exact ⟨((blInterpretationJ H).component r' hr').down.elim
          fun _ himp => ⟨⟨⟩, fun hs =>
            himp ((foldJ_emb_valid H (BLRule.tops r')).mp hs)⟩⟩
    | .extend _ _ e _, hws => by
        exact ⟨⟨⟨⟩, fun hs => Sequent.semanticallyValid_extend
          e.wireExtends e.appsIncluded hws hs.1⟩⟩

/-- **The semantics off the many-object presentation**: one promoted
functor for all hypernet contexts and their extension arrows at once
(the single-context story mints one per hypernet). -/
noncomputable def qtslSemBLM :
    LaxDoubleFunctor (FreePromotion (Presented blPresentationM))
      (ImplDouble BLHCtx) :=
  blMInterpretation.sem fun m n f g => ImplDouble.cell_subsingleton m n f g

/-- The judgment-layer semantics off the many-object presentation. -/
noncomputable def qtslSemBLMJ :
    LaxDoubleFunctor (FreePromotion (Presented blPresentationM))
      BLJudgM :=
  blMInterpretationJ.sem fun m n f g => JudgLayer.cell_subsingleton m n f g

/-!
## The product-lattice rule, derived

`citeFacet s0 rider` over the target context is extend-then-weaken:
transport `s0` along the extension arrow, then weaken its premise by
the rider.  The derivation below splices the `extend` generator into
the embedded weakening by simultaneous substitution; the disjoint-union
inclusion legs instantiate the arrow, and the batch lemma folds the
resulting cells over the product blocks.
-/

/-- The extend-transport instance along `e`, as a rule. -/
def extendRule {a b : BLHCtx} (e : a ⟶ b) (seq : Sequent) : BLMRule :=
  .extend a b e seq

/-- The extend-transport generator as a standalone derivation. -/
def extendDeriv {a b : BLHCtx} (e : a ⟶ b) (seq : Sequent)
    (hws : seq.wellScoped a.ctx) :
    DerivT blPresentationM (.single seq) seq e e :=
  DerivT.gen (P := blPresentationM) (extendRule e seq) hws

/-- The weakening instance producing a cite facet: `citeFacet s0 rider`
from `s0`, at the context `H`. -/
def citeWeakenRule (H : Hypernet) (s0 : Sequent) (rider : Formula) :
    BLMRule :=
  .emb H (.weaken (citeFacet s0 rider) s0 rider)

/-- The cite weakening's side conditions hold definitionally:
`citeFacet` is the weakened form. -/
theorem citeWeakenRule_gate (H : Hypernet) (s0 : Sequent)
    (rider : Formula) :
    blPresentationM.gate (citeWeakenRule H s0 rider) :=
  ⟨rfl, rfl⟩

/-- **The cite derivation**: extend-then-weaken — the `extend`
generator along `e` spliced into the embedded weakening at the target
context by simultaneous substitution.  The first derivation in this
development whose boundary tight arrows are nonidentity.  (The
substitution's composite boundary `e ≫ 𝟙 b` is definitionally `e`:
field-wise composition, function eta, structure eta.) -/
def citeDeriv {a b : BLHCtx} (e : a ⟶ b) (s0 : Sequent) (rider : Formula)
    (hws : s0.wellScoped a.ctx) :
    DerivT blPresentationM (.single s0) (citeFacet s0 rider) e e :=
  DerivT.subst
    (DerivT.gen (P := blPresentationM) (citeWeakenRule b.ctx s0 rider)
      (citeWeakenRule_gate b.ctx s0 rider))
    (DerivSeqT.cons (extendDeriv e s0 hws) (DerivSeqT.nil e))

/-- The cite derivation's premise string over the presented carrier. -/
def citeTops {a : BLHCtx} (s0 : Sequent) :
    LoosePath (VirtualDoubleCategoryData.Loose
      (C := Presented blPresentationM)) (.of a) (.of a) :=
  .single (s0 : Sequent)

/-- The cite derivation as a multicell of the presented virtual double
category, framed by the extension arrow on both tight sides. -/
def citeCell {a b : BLHCtx} (e : a ⟶ b) (s0 : Sequent) (rider : Formula)
    (hws : s0.wellScoped a.ctx) :
    VirtualDoubleCategoryData.Cell (C := Presented blPresentationM)
      (citeTops s0)
      ((citeFacet s0 rider) :
        VirtualDoubleCategoryData.Loose (.of b) (.of b))
      (e : Presented.of a ⟶ Presented.of b) e := by
  exact ⟨⟨citeDeriv e s0 rider hws⟩⟩

/-- The cite derivation's covering, as a cell of the free promotion —
its tight sides are the extension arrow, not an identity. -/
def citeCovering {x y : BLHCtx} (e : x ⟶ y) (s0 : Sequent)
    (rider : Formula) (hws : s0.wellScoped x.ctx) :
    PseudoDoubleCategoryStruct.Cell
      (C := FreePromotion (Presented blPresentationM))
      (a := .of (.of x)) (b := .of (.of x))
      (c := .of (.of y)) (d := .of (.of y))
      (citeTops s0)
      (LoosePath.single ((citeFacet s0 rider) :
        VirtualDoubleCategoryData.Loose (Presented.of y) (Presented.of y)))
      (e : FreePromotion.of (Presented.of x) ⟶ .of (.of y)) e := by
  exact ⟨⟨(VirtualDoubleCategoryStruct.CellSeq.singleton
    (citeCell e s0 rider hws)).castDom (LoosePath.comp_nil _)⟩⟩

/-- **The cite step, through the promoted functor**: from the validity
of `s0` over the source context, the validity of `citeFacet s0 rider`
over the target context — the proof term routed through `mapCell` of
the many-object semantics on the cite covering.  (The independent
statement this route recovers is `sound_productLattice_citeLeft/Right`;
those lemmas are never cited here.) -/
theorem cite_valid_through_M {a b : BLHCtx} (e : a ⟶ b) (s0 : Sequent)
    (rider : Formula) (hws : s0.wellScoped a.ctx)
    (hval : s0.semanticallyValid a.ctx) :
    (citeFacet s0 rider).semanticallyValid b.ctx := by
  have himp := (qtslSemBLM.mapCell (citeCovering e s0 rider hws)).down
  exact (himp ⟨hval, trivial⟩).1

/-- The cite step through the judgment-layer route: same covering, same
endpoint, the other carrier. -/
theorem cite_valid_through_MJ {a b : BLHCtx} (e : a ⟶ b) (s0 : Sequent)
    (rider : Formula) (hws : s0.wellScoped a.ctx)
    (hval : s0.semanticallyValid a.ctx) :
    (citeFacet s0 rider).semanticallyValid b.ctx := by
  obtain ⟨_, himp⟩ := (qtslSemBLMJ.mapCell (citeCovering e s0 rider hws)).down
  exact (himp ⟨hval, trivial⟩).1

/-- **The cite step at the checker face**: factor-premise validity in,
extended-context facet face out. -/
theorem cite_face_through_promotionM {a b : BLHCtx} (e : a ⟶ b)
    (s0 : Sequent) (rider : Formula) (hws : s0.wellScoped a.ctx)
    (hval : s0.semanticallyValid a.ctx) :
    Plain.upperProb (Plain.admCyl b.ctx (citeFacet s0 rider))
      (Plain.postEvt b.ctx (citeFacet s0 rider))ᶜ = 0 :=
  (Plain.semanticallyValid_iff_face b.ctx (citeFacet s0 rider)).mp
    (cite_valid_through_M e s0 rider hws hval)

/-- The cite step at the checker face, judgment-layer route. -/
theorem cite_face_through_promotionMJ {a b : BLHCtx} (e : a ⟶ b)
    (s0 : Sequent) (rider : Formula) (hws : s0.wellScoped a.ctx)
    (hval : s0.semanticallyValid a.ctx) :
    Plain.upperProb (Plain.admCyl b.ctx (citeFacet s0 rider))
      (Plain.postEvt b.ctx (citeFacet s0 rider))ᶜ = 0 :=
  (Plain.semanticallyValid_iff_face b.ctx (citeFacet s0 rider)).mp
    (cite_valid_through_MJ e s0 rider hws hval)

/-!
## The disjoint-union instances and the batch lemma
-/

/-- The left inclusion of a disjoint union, as an extension arrow. -/
def extLeft {H1 H2 : Hypernet} (hd : H1.WireDisjoint H2) :
    BLHCtx.of H1 ⟶ BLHCtx.of (H1.disjUnion H2 hd) :=
  ⟨Hypernet.disjUnion_wireExtends_left hd,
   fun _ happ => List.mem_append_left _ happ⟩

/-- The right inclusion of a disjoint union, as an extension arrow. -/
def extRight {H1 H2 : Hypernet} (hd : H1.WireDisjoint H2) :
    BLHCtx.of H2 ⟶ BLHCtx.of (H1.disjUnion H2 hd) :=
  ⟨Hypernet.disjUnion_wireExtends_right hd,
   fun _ happ => List.mem_append_right _ happ⟩

/-- The left cite of the product-lattice rule, at the checker face:
validity of a facet over the LEFT FACTOR yields the face of its cited
facet over the disjoint union. -/
theorem citeLeft_face_through_promotionM {H1 H2 : Hypernet}
    (hd : H1.WireDisjoint H2) (s0 : Sequent) (rider : Formula)
    (hws : s0.wellScoped H1) (hval : s0.semanticallyValid H1) :
    Plain.upperProb
      (Plain.admCyl (H1.disjUnion H2 hd) (citeFacet s0 rider))
      (Plain.postEvt (H1.disjUnion H2 hd) (citeFacet s0 rider))ᶜ = 0 :=
  cite_face_through_promotionM (extLeft hd) s0 rider hws hval

/-- The right cite of the product-lattice rule, at the checker face. -/
theorem citeRight_face_through_promotionM {H1 H2 : Hypernet}
    (hd : H1.WireDisjoint H2) (s0 : Sequent) (rider : Formula)
    (hws : s0.wellScoped H2) (hval : s0.semanticallyValid H2) :
    Plain.upperProb
      (Plain.admCyl (H1.disjUnion H2 hd) (citeFacet s0 rider))
      (Plain.postEvt (H1.disjUnion H2 hd) (citeFacet s0 rider))ᶜ = 0 :=
  cite_face_through_promotionM (extRight hd) s0 rider hws hval

/-- The left cite at the checker face, judgment-layer route. -/
theorem citeLeft_face_through_promotionMJ {H1 H2 : Hypernet}
    (hd : H1.WireDisjoint H2) (s0 : Sequent) (rider : Formula)
    (hws : s0.wellScoped H1) (hval : s0.semanticallyValid H1) :
    Plain.upperProb
      (Plain.admCyl (H1.disjUnion H2 hd) (citeFacet s0 rider))
      (Plain.postEvt (H1.disjUnion H2 hd) (citeFacet s0 rider))ᶜ = 0 :=
  cite_face_through_promotionMJ (extLeft hd) s0 rider hws hval

/-- The right cite at the checker face, judgment-layer route. -/
theorem citeRight_face_through_promotionMJ {H1 H2 : Hypernet}
    (hd : H1.WireDisjoint H2) (s0 : Sequent) (rider : Formula)
    (hws : s0.wellScoped H2) (hval : s0.semanticallyValid H2) :
    Plain.upperProb
      (Plain.admCyl (H1.disjUnion H2 hd) (citeFacet s0 rider))
      (Plain.postEvt (H1.disjUnion H2 hd) (citeFacet s0 rider))ᶜ = 0 :=
  cite_face_through_promotionMJ (extRight hd) s0 rider hws hval

/-- **The batch lemma, derived**: the statement of
`sound_productLattice`, with every facet's validity routed through the
promoted functor — a fold of cite cells over the product blocks, no new
generator (the derivation elaborates into `extend` and the wired
weakening). -/
theorem sound_productLattice_through_M {H1 H2 : Hypernet}
    (d : PProductLatticeData H1 H2)
    (hL : d.left.Valid) (hR : d.right.Valid) :
    ∀ b ∈ d.prodBlocks, ∀ s ∈ b.facets,
      s.semanticallyValid (H1.disjUnion H2 d.disjoint) := by
  intro b hb s hs
  obtain ⟨b1, hb1, b2, hb2, rfl⟩ :
      ∃ b1 ∈ d.left.blocks, ∃ b2 ∈ d.right.blocks, prodBlock b1 b2 = b := by
    simpa [PProductLatticeData.prodBlocks] using hb
  rcases List.mem_append.mp hs with hsl | hsr
  · obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hsl
    exact cite_valid_through_M (extLeft d.disjoint) s0 b2.region
      (d.left.facetsScoped b1 hb1 s0 hs0) (hL b1 hb1 s0 hs0)
  · obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hsr
    exact cite_valid_through_M (extRight d.disjoint) s0 b1.region
      (d.right.facetsScoped b2 hb2 s0 hs0) (hR b2 hb2 s0 hs0)

/-- The batch lemma through the judgment-layer route. -/
theorem sound_productLattice_through_MJ {H1 H2 : Hypernet}
    (d : PProductLatticeData H1 H2)
    (hL : d.left.Valid) (hR : d.right.Valid) :
    ∀ b ∈ d.prodBlocks, ∀ s ∈ b.facets,
      s.semanticallyValid (H1.disjUnion H2 d.disjoint) := by
  intro b hb s hs
  obtain ⟨b1, hb1, b2, hb2, rfl⟩ :
      ∃ b1 ∈ d.left.blocks, ∃ b2 ∈ d.right.blocks, prodBlock b1 b2 = b := by
    simpa [PProductLatticeData.prodBlocks] using hb
  rcases List.mem_append.mp hs with hsl | hsr
  · obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hsl
    exact cite_valid_through_MJ (extLeft d.disjoint) s0 b2.region
      (d.left.facetsScoped b1 hb1 s0 hs0) (hL b1 hb1 s0 hs0)
  · obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hsr
    exact cite_valid_through_MJ (extRight d.disjoint) s0 b1.region
      (d.right.facetsScoped b2 hb2 s0 hs0) (hR b2 hb2 s0 hs0)

/-!
## The two-factor fixture, concrete

`Qtsl.ProductLattice`'s own demonstration pair (`ProductLatticeDemo`:
two single-wire hypernets on distinct wires, certified block lattices
over each) driven through the many-object carrier to the checker face
over their disjoint union, with every premise discharged by the demo's
own lemmas — zero hypotheses.  Honest note, preregistered: the demo
facets are wire-free (constant formulas), so these corollaries exercise
the route end to end but are transport-degenerate; the generic
theorems above (arbitrary well-scoped `s0`) carry the transport
content. -/

open ProductLatticeDemo in
/-- The demo's left join facet at the checker face over the union,
through the many-object carrier — no validity hypotheses. -/
theorem demoJoinFacetX_face_through_promotionM :
    Plain.upperProb
      (Plain.admCyl (Hx.disjUnion Hy HxHy_disjoint)
        (citeFacet facetA1 riderJx))
      (Plain.postEvt (Hx.disjUnion Hy HxHy_disjoint)
        (citeFacet facetA1 riderJx))ᶜ = 0 :=
  citeLeft_face_through_promotionM HxHy_disjoint facetA1 riderJx
    facetA1_wellScoped facetA1_valid

open ProductLatticeDemo in
/-- The demo's right join facet at the checker face over the union,
through the many-object carrier — no validity hypotheses. -/
theorem demoJoinFacetY_face_through_promotionM :
    Plain.upperProb
      (Plain.admCyl (Hx.disjUnion Hy HxHy_disjoint)
        (citeFacet facetA2 riderJy))
      (Plain.postEvt (Hx.disjUnion Hy HxHy_disjoint)
        (citeFacet facetA2 riderJy))ᶜ = 0 :=
  citeRight_face_through_promotionM HxHy_disjoint facetA2 riderJy
    facetA2_wellScoped facetA2_valid

open ProductLatticeDemo in
/-- The demo's left join facet, judgment-layer route. -/
theorem demoJoinFacetX_face_through_promotionMJ :
    Plain.upperProb
      (Plain.admCyl (Hx.disjUnion Hy HxHy_disjoint)
        (citeFacet facetA1 riderJx))
      (Plain.postEvt (Hx.disjUnion Hy HxHy_disjoint)
        (citeFacet facetA1 riderJx))ᶜ = 0 :=
  citeLeft_face_through_promotionMJ HxHy_disjoint facetA1 riderJx
    facetA1_wellScoped facetA1_valid

open ProductLatticeDemo in
/-- The demo's right join facet, judgment-layer route. -/
theorem demoJoinFacetY_face_through_promotionMJ :
    Plain.upperProb
      (Plain.admCyl (Hx.disjUnion Hy HxHy_disjoint)
        (citeFacet facetA2 riderJy))
      (Plain.postEvt (Hx.disjUnion Hy HxHy_disjoint)
        (citeFacet facetA2 riderJy))ᶜ = 0 :=
  citeRight_face_through_promotionMJ HxHy_disjoint facetA2 riderJy
    facetA2_wellScoped facetA2_valid

end QtslSem

end SuFunctor
