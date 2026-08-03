import SuFunctor.Adequacy.CheckerAcceptance

/-! # Axiom audit for acceptance as a semantic-universe theorem

Prints the axiom footprint of the composed corollaries — sealed-byte
acceptance read at the checker face, at the model class, at the record
space, and in the semantic universe's fibre — together with the
reflection route's own soundness theorem they compose with.  Expected
footprint for every entry: at most `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

open SuFunctor.Adequacy

#print axioms PPLC.Geolog.acceptBytesSealed_sound
#print axioms SuFunctor.Adequacy.acceptBytesSealed_face_sound
#print axioms SuFunctor.Adequacy.acceptBytesSealed_modelClass_sound
#print axioms SuFunctor.Adequacy.acceptBytesSealed_face_valWire_sound
#print axioms SuFunctor.Adequacy.acceptBytesSealed_su_sound
