import SuFunctor.Site.CausalConcordance

/-! # Axiom audit for the site concordance

`#print axioms` receipts for the derived-site concordance leg: the
window/diamond identification, the definitional relation
correspondences, the concordance keystone, and the composed wavy-site
correspondence.  The relation-level trio and the round-trips are
expected axiom-free (bare `rfl`/`Iff.rfl`). -/

open SuFunctor.Site SuFunctor.Site.TTT

#print axioms SuFunctor.Site.TTT.Window.toDiamond_ofDiamond
#print axioms SuFunctor.Site.TTT.Window.ofDiamond_toDiamond
#print axioms SuFunctor.Site.TTT.Window.le_iff
#print axioms SuFunctor.Site.TTT.Window.ofDiamond_le_iff
#print axioms SuFunctor.Site.TTT.Window.strictlyInterior_iff
#print axioms SuFunctor.Site.TTT.Window.strictlyInterior_ofDiamond_iff
#print axioms SuFunctor.Site.TTT.Window.monotone_toDiamond
#print axioms SuFunctor.Site.TTT.windowToDiamond
#print axioms SuFunctor.Site.TTT.mem_interiorTopology_iff_derived
#print axioms SuFunctor.Site.TTT.wavy_mem_iff_derived
