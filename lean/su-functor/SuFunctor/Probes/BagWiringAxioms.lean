import SuFunctor.Adequacy.BagWiring

/-! # Axiom audit for the bag square's semantic-universe wiring

Prints the axiom footprint of the bag wiring layer: the pushforward
composition laws, the law-level exchange statics and section lift, the
one-step commuting square with its section-independence, and the wired
square with its option-A corner and slice corollary.  Expected
footprint for every entry: `propext`, `Classical.choice`, `Quot.sound`
— the standard three, no `sorryAx`, nothing else. -/

open SuFunctor SuFunctor.Adequacy

#print axioms SuFunctor.SubPMF.map_id
#print axioms SuFunctor.SubPMF.map_map
#print axioms SuFunctor.Adequacy.toSymSigma_bagRelabel
#print axioms SuFunctor.Adequacy.map_toSymSigma_bagRelabel
#print axioms SuFunctor.Adequacy.idealPoint_collective_bagRelabel
#print axioms SuFunctor.Adequacy.map_symSecSigma_reading
#print axioms SuFunctor.Adequacy.exists_ordered_reading
#print axioms SuFunctor.Adequacy.collectiveStep_toSymSigma
#print axioms SuFunctor.Adequacy.collectiveStep_section_congr
#print axioms SuFunctor.Adequacy.su_bag_adequacy
#print axioms SuFunctor.Adequacy.su_bag_reading_mem
#print axioms SuFunctor.Adequacy.su_bag_bottom
#print axioms SuFunctor.Adequacy.su_bag_slice
