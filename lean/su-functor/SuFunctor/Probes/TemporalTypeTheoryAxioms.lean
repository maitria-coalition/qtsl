import SuFunctor.Site.TemporalTypeTheory
import SuFunctor.Site.BehaviorSpec

/-! # Axiom audit for the temporal-type-theory inclusion

`#print axioms` receipts for the site-level leg (the interval base
site, the anchor quotient, the discrete-fibration lifts, the cover
correspondence, the trajectory identification) and the spec-level leg
(the indicator calculus, the behavior-spec object, the judgment
bridge, the transport intertwining, the compositor identification). -/

open SuFunctor.Site SuFunctor.Site.TTT

-- site-level leg
#print axioms SuFunctor.Site.TTT.anchorQuot
#print axioms SuFunctor.Site.TTT.anchorQuot_obj_surjective
#print axioms SuFunctor.Site.TTT.existsUnique_lift_up
#print axioms SuFunctor.Site.TTT.existsUnique_lift_down
#print axioms SuFunctor.Site.TTT.wavy_iff_strictlyInterior
#print axioms SuFunctor.Site.TTT.ssTraj
#print axioms SuFunctor.Site.TTT.windowTraj
#print axioms SuFunctor.Site.TTT.anchorTrajIso
#print axioms SuFunctor.Site.TTT.behaviorPullback

-- spec-level leg
#print axioms SuFunctor.Site.support_push_eq_image
#print axioms SuFunctor.Site.pull_indPen
#print axioms SuFunctor.Site.indPen_add_indPen_apply
#print axioms SuFunctor.Site.isPersistent_specOfBehavior
#print axioms SuFunctor.Site.satAt_specOfBehavior_iff
#print axioms SuFunctor.Site.satAt_specOfBehavior_mono
#print axioms SuFunctor.Site.ttObject
#print axioms SuFunctor.Site.wSpecMap_specOfBehavior
#print axioms SuFunctor.Site.boxplusW_indPen
#print axioms SuFunctor.Site.cplOfBehavior_glue_subset_wComp
#print axioms SuFunctor.Site.satAt_wComp_iff_glue
