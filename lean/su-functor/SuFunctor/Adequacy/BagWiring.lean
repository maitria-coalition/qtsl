import SuFunctor.Adequacy.RecordSpace
import SuFunctor.Adequacy.Bag

/-! # The bag square, wired to the semantic universe

The bag former's adequacy content — token order is non-semantic, and
the canonical sorted representative is bookkeeping, not meaning — read
at the semantic universe's judgment, in the sibling-square idiom of
`SuFunctor.Adequacy.SemanticUniverseWiring`.

**The stratum boundary, stated rather than smoothed.**  The judgment's
citizens are exact-rational laws (`SubPMF`), entering as ideal points;
the exchange-quotient transport core (`SuFunctor.Adequacy.Bag`) states
its chain layer over Measure-valued kernels, which cannot enter the
judgment as ideal points, and no comparison functor between the two law
stocks exists in this tree.  What the wiring therefore consumes from
the core is its measure-free layer — the quotient/section statics
(`toSymSigma`, `symSecSigma`, their inverse laws, sorting's
permutation-invariance) — and what it re-states at the exact stratum is
the **one-step generating cell** of the square: the `SubPMF` faces of
`quotKernel_comp_eq` (the one-step commuting square) and
`comap_section_congr` (section-independence).  Three exact-stratum
facts, then the judgment:

* **One collective reading per exchange orbit**
  (`map_toSymSigma_bagRelabel`): pushing a law along a per-shape token
  permutation does not move its collective reading — the law-level
  shadow of the interface stratum's exchange action
  (`SuFunctor.BagFormer.bagPerm`, whose spec-tier face is
  `ExchangeInvariant` there).

* **Every collective law is a reading** (`exists_ordered_reading`): the
  canonical section lifts a collective law to an ordered one and the
  lift reads back (`map_symSecSigma_reading`) — the judgment's
  collective citizens are exactly the ordered stratum's shadows.

* **The one-step square** (`collectiveStep_toSymSigma`): for an
  exchange-invariant ordered step, the collective step compiled through
  the canonical section — `collectiveStep`, the exact-stratum face of
  `quotKernel` — reads back the direct collective pushforward of the
  ordered dynamics, at every ordered state; and any section of the
  quotient induces the same collective step
  (`collectiveStep_section_congr`): the canonical representative is a
  presentation choice, exactly as at the measure stratum.

The judgment tie is then the one-atom-projection idiom of the demonic
corners: the compiled presentation (`bagStepDnf`) pins the
section-compiled collective step, and **`su_bag_adequacy`** says the
ideal point of a law models it, at an ordered state's class, exactly
when the law is the ordered dynamics' direct collective reading — token
order and the canonical-representative bookkeeping are both invisible
at the judgment.  The donor accessories ride along: positive face,
ex-falso corner, the slice reading (under a nonzero collective step —
no mass discipline is assumed of the ordered dynamics), and
order-invariance of verdicts (`idealPoint_collective_bagRelabel`).

Deliberately NOT here, each naming its home: the finite-horizon closure
at the exact stratum — iterates need a kernel composition (`SubPMF`
bind) the exact stratum does not yet carry, and the finite-horizon
content is already mechanized at the measure stratum
(`iter_intertwine`, `bag_transport`), this tree's standing quarantine
of the analytic floor; law-level completeness of the collective reading
— a mixture may spread over several exchange orbits, so distinct
ordered laws share a reading without any single permutation relating
them (the pointwise completeness is the core's `fiber_exists_perm`, and
it is a statement about carriers, not laws); and the record-space wire
object for the collective carrier, which is the record-space stratum's
own construction site. -/

namespace SuFunctor

universe u

/-! ## Pushforward functoriality (the two missing composition laws) -/

namespace SubPMF

variable {X Y Z : Type u}

/-- Pushforward along the identity relabels nothing. -/
theorem map_id (μ : SubPMF X) : μ.map (id : X → X) = μ :=
  SubPMF.ext' (by rw [map_wt, Finsupp.mapDomain_id])

/-- Pushforward is functorial: relabeling twice is relabeling along
the composite. -/
theorem map_map (f : X → Y) (g : Y → Z) (μ : SubPMF X) :
    (μ.map f).map g = μ.map (g ∘ f) :=
  SubPMF.ext' (by rw [map_wt, map_wt, map_wt, Finsupp.mapDomain_comp])

end SubPMF

namespace Adequacy

open SuFunctor.Universe (SpecDnf)
open Bag

/-! ## The exchange action at the law level -/

section Relabel

variable {B : Type u}

/-- The exchange relabeling of the shape-indexed bag carrier: permute
token indices per shape — the state-space face of the interface
stratum's exchange action (`SuFunctor.BagFormer.bagPerm`). -/
def bagRelabel (σ : ∀ n, Equiv.Perm (Fin n)) :
    BagPoints B → BagPoints B :=
  fun p => ⟨p.1, p.2 ∘ σ p.1⟩

/-- The quotient forgets the relabeling — pointwise. -/
theorem toSymSigma_bagRelabel (σ : ∀ n, Equiv.Perm (Fin n))
    (p : BagPoints B) :
    toSymSigma (bagRelabel σ p) = toSymSigma p := by
  obtain ⟨n, x⟩ := p
  exact congrArg (Sigma.mk n) (toSym_comp_perm x (σ n))

/-- **One collective reading per exchange orbit**: pushing an ordered
law along an exchange relabeling does not move its collective
reading.  (The converse fails at the law level: a mixture may spread
over several orbits — the pointwise completeness is the transport
core's `fiber_exists_perm`.) -/
theorem map_toSymSigma_bagRelabel (σ : ∀ n, Equiv.Perm (Fin n))
    (μ : SubPMF (BagPoints B)) :
    (μ.map (bagRelabel σ)).map toSymSigma = μ.map toSymSigma := by
  rw [SubPMF.map_map]
  have h : (toSymSigma ∘ bagRelabel σ : BagPoints B → SymPoints B)
      = toSymSigma :=
    funext (toSymSigma_bagRelabel σ)
  rw [h]

/-- **Token order is non-semantic at the judgment**: exchange-related
ordered laws have one collective reading, hence one ideal point and
one verdict against every presented diagram over the collective
carrier. -/
theorem idealPoint_collective_bagRelabel (σ : ∀ n, Equiv.Perm (Fin n))
    (μ : SubPMF (BagPoints B))
    (L : List (SubPMF (SymPoints B) → Prop)) :
    idealPoint ((μ.map (bagRelabel σ)).map toSymSigma)
        ∈ (diagramDnf L).modelClass
      ↔ idealPoint (μ.map toSymSigma) ∈ (diagramDnf L).modelClass := by
  rw [map_toSymSigma_bagRelabel σ μ]

end Relabel

/-! ## The canonical section at the law level -/

section SectionLift

variable {B : Type u} [LinearOrder B]

/-- The canonical lift reads back: quotienting after sectioning is the
identity on collective laws — the law-level face of
`toSymSigma_symSecSigma`. -/
theorem map_symSecSigma_reading (ν : SubPMF (SymPoints B)) :
    (ν.map symSecSigma).map toSymSigma = ν := by
  rw [SubPMF.map_map]
  have h : (toSymSigma ∘ symSecSigma : SymPoints B → SymPoints B)
      = id :=
    funext toSymSigma_symSecSigma
  rw [h, SubPMF.map_id]

/-- **Every collective law is a collective reading**: the canonical
section lifts it to an ordered law whose reading it is — the
judgment's collective citizens are exactly the ordered stratum's
shadows. -/
theorem exists_ordered_reading (ν : SubPMF (SymPoints B)) :
    ∃ μ : SubPMF (BagPoints B), μ.map toSymSigma = ν :=
  ⟨ν.map symSecSigma, map_symSecSigma_reading ν⟩

end SectionLift

/-! ## The one-step square at the exact stratum -/

section CollectiveStep

variable {B : Type u}

/-- Exchange-invariance of an ordered step, in permutation form: the
collective reading of the step ignores per-shape token permutations —
the exact-stratum sibling of the transport core's invariance
hypothesis (`bag_transport`'s `hK`), interderivable there with
invariance under canonicalization (`invariance_iff_perm`). -/
def ExchangeStep (K : BagPoints B → SubPMF (BagPoints B)) : Prop :=
  ∀ (n : ℕ) (x : Fin n → B) (σ : Equiv.Perm (Fin n)),
    (K ⟨n, x ∘ σ⟩).map toSymSigma = (K ⟨n, x⟩).map toSymSigma

variable [LinearOrder B]

/-- The collective one-step dynamics: read the collective state
through the canonical section, step the ordered dynamics, read the
outcome collectively — the exact-stratum face of the transport core's
`quotKernel`. -/
noncomputable def collectiveStep
    (K : BagPoints B → SubPMF (BagPoints B)) :
    SymPoints B → SubPMF (SymPoints B) :=
  fun m => (K (symSecSigma m)).map toSymSigma

/-- **The one-step commuting square** (the `SubPMF` face of
`quotKernel_comp_eq`): for an exchange-invariant ordered step, the
section-compiled collective step at an ordered state's class is the
direct collective reading of the ordered step — canonicalization
costs nothing, because the canonical representative is a permutation
of the state (`symSecSigma_toSymSigma` + sorting's permutation
form). -/
theorem collectiveStep_toSymSigma
    {K : BagPoints B → SubPMF (BagPoints B)} (hK : ExchangeStep K)
    (p : BagPoints B) :
    collectiveStep K (toSymSigma p) = (K p).map toSymSigma := by
  obtain ⟨n, x⟩ := p
  show (K (symSecSigma (toSymSigma ⟨n, x⟩))).map toSymSigma = _
  rw [symSecSigma_toSymSigma]
  exact hK n x (Tuple.sort x)

/-- **Section-independence** (the `SubPMF` face of
`comap_section_congr`): any section of the quotient induces the same
collective step — the canonical representative is a presentation
choice, not a semantic input. -/
theorem collectiveStep_section_congr
    {K : BagPoints B → SubPMF (BagPoints B)} (hK : ExchangeStep K)
    {s' : SymPoints B → BagPoints B}
    (hs' : ∀ m, toSymSigma (s' m) = m) (m : SymPoints B) :
    (K (s' m)).map toSymSigma = collectiveStep K m := by
  calc (K (s' m)).map toSymSigma
      = collectiveStep K (toSymSigma (s' m)) :=
        (collectiveStep_toSymSigma hK (s' m)).symm
    _ = collectiveStep K m := by rw [hs' m]

end CollectiveStep

/-! ## The bag square, wired -/

section BagWiring

variable {B : Type u} [LinearOrder B]

/-- The bag former's compiled presentation at the collective carrier:
the one-atom projection pinning the section-compiled collective step —
the presentation stratum's working data (canonical representatives)
entering the fibre as a single wall atom, exactly as the demonic
corners' set-valued faces do. -/
noncomputable def bagStepDnf (K : BagPoints B → SubPMF (BagPoints B))
    (m : SymPoints B) : SpecDnf (Plain.Joint (SymPoints B)) :=
  diagramDnf [singletonC (collectiveStep K m)]

/-- **The bag square, wired to the semantic universe — the one-step
generating cell**: the ideal point of a collective law models the
section-compiled presentation at an ordered state's class exactly when
the law is the direct collective reading of the ordered dynamics at
that state.  Token order and the canonical-representative bookkeeping
are both invisible at the judgment; the finite-horizon closure of this
cell is the measure stratum's `bag_transport`. -/
theorem su_bag_adequacy
    {K : BagPoints B → SubPMF (BagPoints B)} (hK : ExchangeStep K)
    (p : BagPoints B) (ν : SubPMF (SymPoints B)) :
    idealPoint ν ∈ (bagStepDnf K (toSymSigma p)).modelClass
      ↔ ν = (K p).map toSymSigma := by
  have h := idealPoint_mem_diagramDnf_iff
    [singletonC (collectiveStep K (toSymSigma p))] ν
  constructor
  · intro hm
    obtain ⟨h1, -⟩ := h.mp hm
    rw [singletonC_iff] at h1
    exact h1.trans (collectiveStep_toSymSigma hK p)
  · intro he
    exact h.mpr
      ⟨he.trans (collectiveStep_toSymSigma hK p).symm, trivial⟩

/-- The positive face: the ordered dynamics' collective reading models
its compiled presentation. -/
theorem su_bag_reading_mem
    {K : BagPoints B → SubPMF (BagPoints B)} (hK : ExchangeStep K)
    (p : BagPoints B) :
    idealPoint ((K p).map toSymSigma)
      ∈ (bagStepDnf K (toSymSigma p)).modelClass :=
  (su_bag_adequacy hK p ((K p).map toSymSigma)).mpr rfl

/-- Ex falso at the bag's corner: the inconsistent system models no
compiled presentation. -/
theorem su_bag_bottom (K : BagPoints B → SubPMF (BagPoints B))
    (m : SymPoints B) :
    (⊤ : Plain.Pen (SymPoints B)) ∉ (bagStepDnf K m).modelClass :=
  top_notMem_diagramDnf _

/-- The credal reading at the bag's corner, through the slice: under a
nonzero collective step (no mass discipline is assumed of the ordered
dynamics), membership at the judgment is exactly radial maximality in
the reading's credal ray. -/
theorem su_bag_slice
    {K : BagPoints B → SubPMF (BagPoints B)} (hK : ExchangeStep K)
    (p : BagPoints B)
    (hne : (K p).map toSymSigma ≠ SubPMF.zero (SymPoints B))
    (ν : SubPMF (SymPoints B)) :
    idealPoint ν ∈ (bagStepDnf K (toSymSigma p)).modelClass
      ↔ maxSlice (rayC ((K p).map toSymSigma)) ν :=
  (su_bag_adequacy hK p ν).trans (maxSlice_rayC hne ν).symm

end BagWiring

end Adequacy

end SuFunctor
