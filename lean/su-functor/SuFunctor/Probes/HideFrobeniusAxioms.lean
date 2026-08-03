import SuFunctor.Universe.HideFrobenius

/-! # Axiom audit for the hide-Frobenius adjudication

Prints the axiom footprint of the Frobenius adjudication for the
reflected existential: the propositional identities for the raw
inf-projection, the envelope-of-a-wall structure lemma, the lax law
(the canonical comparison), equality under the inf-compactness
certificate, and the refutation witnesses (equality failure and its
judgment-visible sharpening, both conjunctions).  Expected footprint for
every entry: `propext`, `Classical.choice`, `Quot.sound` — the standard
three, no `sorryAx`, nothing else. -/

open SuFunctor.Universe

-- propositional stratum: the raw inf-projection satisfies Frobenius
#print axioms SuFunctor.Universe.infProj_sup_comp
#print axioms SuFunctor.Universe.infProj_add_comp
-- envelope structure: the envelope of a wall is the wall of the closure
#print axioms SuFunctor.Universe.lscEnv_charFn
-- the lax law: the canonical comparison always holds
#print axioms SuFunctor.Universe.hide_sup_le
#print axioms SuFunctor.Universe.hide_add_le
-- equality under the inf-compactness certificate
#print axioms SuFunctor.Universe.hide_sup_comp
#print axioms SuFunctor.Universe.hide_add_comp
-- the refutation: equality fails through the reflector…
#print axioms SuFunctor.Universe.exists_lowerSemicontinuous_hide_add_ne
#print axioms SuFunctor.Universe.exists_lowerSemicontinuous_hide_sup_ne
-- …and the failure is judgment-visible
#print axioms SuFunctor.Universe.exists_judgment_separating_hide_add
#print axioms SuFunctor.Universe.exists_judgment_separating_hide_sup
