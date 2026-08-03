import SuFunctor.Site.GeneralWindow

/-! # Axiom audit for the general-stratum window assembly

Prints the axiom footprint of the site-direction calculus over
subprobability Borel joints: measurability of the two transport
directions, the window-extension presheaf laws, the two exchange
theorems, the persistence discipline and its closure package, and the
seam theorems exhibiting the exact assembly as a sub-instance of the
general one.  Expected footprint for every entry: `propext`,
`Classical.choice`, `Quot.sound` — the standard three, no `sorryAx`,
nothing else. -/

open SuFunctor.Site

#print axioms SuFunctor.Site.measurable_trajRes
#print axioms SuFunctor.Site.measurable_trajMap
#print axioms SuFunctor.Site.penExtM_refl
#print axioms SuFunctor.Site.penExtM_penExtM
#print axioms SuFunctor.Site.penExtM_pull_trajMap
#print axioms SuFunctor.Site.penExtM_mboxplusW
#print axioms SuFunctor.Site.penExtM_munitPenW
#print axioms SuFunctor.Site.IsMatchingM.isPersistentM
#print axioms SuFunctor.Site.IsPersistentM.image_pull_trajMap
#print axioms SuFunctor.Site.IsPersistentM.image2_mboxplusW
#print axioms SuFunctor.Site.isPersistentM_munitPenW
#print axioms SuFunctor.Site.penExtM_comp_toMeas
#print axioms SuFunctor.Site.IsPersistentM.seamRestrict
