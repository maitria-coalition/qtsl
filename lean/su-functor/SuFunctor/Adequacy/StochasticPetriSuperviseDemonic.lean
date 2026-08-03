import SuFunctor.Adequacy.StochasticPetriSupervise
import SuFunctor.Adequacy.MaDemonic
import SuFunctor.Adequacy.RecordSpace

/-! # Supervision: the collapsed square and the demonic gate-envelope

The adequacy faces of the `Supervise` composition pattern, at the
uncoloured stratum — rungs 3 and 4 of the supervision
mechanization ladder, on top of the
gating lemmas, census, and controls of
`SuFunctor.Adequacy.StochasticPetriSupervise`.

**The package as data, and the expansion lemma (rung 3).**  A
`GatePlant` is the plant side of a supervised composite: a delay
layer, plant immediate transitions, and a declared gate roster, with
the plant-side census clauses carried as fields.  An `Occupant` of
the plant's policy seat is the update-arc data of a jump-only policy,
with confinement (arcs only on gate places) carried as fields.
`assemble` juxtaposes them into an ordinary `FinISPN` — the enabling-
arc reduction as a function — and the **package-expansion lemma**
(`assemble_arcSeparation`) discharges the `ArcSeparation` census once
for every expansion: the package door of the two-door structure, its
admission check now a theorem rather than a per-composite `decide`.

**The fixed-policy square is an instance, not an extension.**  The
supervised composite is again a net of the fragment, so its adequacy
square is `ispn_cascade_adequacy` *applied to it* —
`fixed_policy_adequacy` and its semantic-universe twin are
deliberately one-line: the r2 memo's collapse (there is nothing to
flatten; the flattening of the r1 design became the identity), now
stated at package generality, with `gnet₂_supervised_adequacy` as its
landed micro-instance.

**The demonic gate-envelope (rung 4).**  The family face quantifies
over the *occupants of the policy seat*, and two structural findings
shape its statement:

* **Heterogeneity is structural.**  The tangible/vanishing split is
  occupant-relative — a wake makes a marking vanishing (`gnet₂`'s
  queue-waiting marking is vanishing; under the empty policy,
  `gnet₃`'s same marking is tangible) — so the members' observed
  processes live on *different* subtypes of one common marking
  space.  The envelope therefore lives on marking trajectories: each
  member's tangible path law is pushed forward along `Subtype.val`
  at the trajectory level (the record-space stratum's `SubPMF.map`,
  reused — this module adds its probability calculus: `prob_map`
  reads events back through the preimage, so `map_mass` keeps every
  member at full mass).
* **No branch-level certificate exists across the seat.**  Within
  one automaton, `BranchZenoFree` already fails at any disabled-
  action stay row; across occupants the obstruction is essential —
  one occupant's mint fires `m₁₀ → m₁₁` and another's drain fires
  `m₁₁ → m₁₀`, both landing vanishing in suitable nets, so a single
  rank would need `r m₁₁ < r m₁₀ < r m₁₁`.  The seat is therefore
  the `CertScheduler` pattern one level up (`CertOccupant`): each
  member bundles its occupant, its scheduler, and **its own** rank —
  exactly the grain `MaDemonic`'s certified-family stratum names as
  the honest object where no uniform certificate exists.  What *is*
  uniform is the landed donor per net: one `CascadeRank` on an
  occupant's composite serves every enabling-respecting scheduler at
  once (`CertOccupant.ofCascadeRank`, packaging
  `zenoFree_of_cascadeRank`), and the certificate stays a witness,
  never data (`law_rank_irrel`).

The envelope itself is `EnvelopeUnion` over the seat —
`GatePlant.demonicLaws` / `demonicCredal`, the union machinery at its
second genuinely dependent index — and the G-mono envelope face falls
out as the union's own structure, in two halves:

* **containment** (`law_mem_demonicLaws`): every well-formed policy's
  closed-loop law is a member — certify safety once against the
  gate-demon and the verdict theorems
  (`satCredal_lower_demonicCredal` and kin) hand it to every
  partially-sighted policy, at both polarities, through the
  equal-mass slice reconciliation (`demonic_maxSlice`, at `m = 1`);
* **roster monotonicity** (`demonicLaws_mono_gates`): fewer gates ⊆
  more gates — occupants inject as the roster grows, because
  confinement weakens and the assembled nets are *definitionally*
  unchanged (`assemble_widen` is `rfl`), so the envelope only grows.
  This is the family-level face of `enabled_mono`'s landed statics
  face.

Liveness over the unrestricted family stays unprovable by
construction, now at family generality: the **empty policy** is an
occupant (`idleOccupant`, on the empty update type), and given a rank
for the plant's own cascades its closed-loop law is a member
(`idle_mem_demonicLaws`) — deliberate idling is inside the envelope,
which is exactly why no throughput claim survives the ∀-over-members
reading wherever a gated transition is load-bearing (`gnet₃_idles` is
the landed specimen).  The zero-model refusal and the empty-seat
vacuity are mechanized as at the automaton face.

Deliberately separate strata, named: the **compiled demonic square
for the seat** — the admission predicate would carry rank witnesses
inside it, the exact grain `MaDemonic` prices and does not build for
the partial-Zeno automaton stratum; this module inherits that
boundary (classical and credal sides built, slice and verdicts
reconciled; the per-member compiled square is rung 3's, and the
per-member scheduler-demonic square is `MaDemonic`'s where the member
is branch-certified).  The **coloured stratum** (observables through
`ObsIface`, event-port fusions, the D10-witness lint on guard
species) rides the pattern-denotational layer and the wire, per the
same ladder.  The **Minifab supervised instrument** waits on the T1
cascade-closure compiler, as for G3. -/

namespace SuFunctor

/-! ## `SubPMF.map`: the event and mass lemmas

The pushforward itself is the record-space stratum's
(`SuFunctor.Adequacy.RecordSpace`: `SubPMF.map`, fiberwise mass
transport by `Finsupp.mapDomain`, with `map_wt` and
`map_injective`).  What the envelope needs beyond it is the
probability calculus: events read back through the preimage
(`prob_map`), so mass is preserved on the nose (`map_mass`) — which
is what the equal-mass slice reconciliation of the envelope
machinery consumes. -/

namespace SubPMF

universe u

variable {V W : Type u}

/-- **Events read back through the preimage**: the pushforward's
probability of a set is the original probability of its preimage —
fiberwise transport loses nothing, for arbitrary `f`. -/
theorem prob_map (f : V → W) (μ : SubPMF V) (S : Set W) :
    (μ.map f).prob S = μ.prob (f ⁻¹' S) := by
  classical
  have key : (Finsupp.mapDomain f μ.wt).sum
        (fun w x => if w ∈ S then x else 0)
      = μ.wt.sum fun v x => if f v ∈ S then x else 0 :=
    Finsupp.sum_mapDomain_index
      (h := fun w x => if w ∈ S then x else 0)
      (fun _ => ite_self 0) (fun _ m₁ m₂ => by split <;> simp)
  calc (μ.map f).prob S
      = (Finsupp.mapDomain f μ.wt).sum
          (fun w x => if w ∈ S then x else 0) := by
        unfold SubPMF.prob
        exact Finset.sum_congr rfl fun w _ => by
          by_cases h : w ∈ S <;> simp [h]
    _ = μ.wt.sum fun v x => if f v ∈ S then x else 0 := key
    _ = μ.prob (f ⁻¹' S) := by
        unfold SubPMF.prob
        exact Finset.sum_congr rfl fun v _ => by
          by_cases h : f v ∈ S <;> simp [h, Set.mem_preimage]

/-- Mass is preserved: the pushforward of a full-mass law has full
mass — the hypothesis the envelope's slice reconciliation spends. -/
theorem map_mass (f : V → W) (μ : SubPMF V) :
    (μ.map f).mass = μ.mass := by
  have h := prob_map f μ Set.univ
  rwa [Set.preimage_univ] at h

/-- The pushforward of a point mass is the point mass at the image. -/
theorem map_dirac (f : V → W) (v : V) :
    (SubPMF.dirac v).map f = SubPMF.dirac (f v) :=
  SubPMF.ext' (Finsupp.mapDomain_single)

end SubPMF

namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Finset

variable {P T Upl Upo : Type} [Fintype P] [DecidableEq P] [Fintype T]
  [Fintype Upl] [Fintype Upo] {B : ℕ}

namespace Supervise

/-! ## The package as data: plant, occupant, expansion -/

/-- **The plant side of a supervised composite**: a delay layer,
plant immediate transitions, and the declared gate roster — with the
plant's half of the arc-separation census carried as fields (no
ordinary arcs at gate places, either species, either direction;
*read* arcs are free, being the gating itself). -/
structure GatePlant (P T Upl : Type) [Fintype P] [DecidableEq P]
    (B : ℕ) where
  /-- The delay layer — wholly the plant's (the policy is jump-only),
  carrying the composite's initial distribution. -/
  delay : FinSPN P T B
  /-- Ordinary input arcs of the plant's immediate transitions. -/
  ipre : Upl → P → ℕ
  /-- Enabling arcs of the plant's immediate transitions (gating
  arcs, where the place is a gate, live here). -/
  iread : Upl → P → ℕ
  /-- Ordinary output arcs of the plant's immediate transitions. -/
  ipost : Upl → P → ℕ
  /-- The gate roster: the policy-owned places. -/
  gates : Finset P
  /-- Census, plant-delay clause (input direction). -/
  delay_pre_sep : ∀ t : T, ∀ p ∈ gates, delay.pre t p = 0
  /-- Census, plant-delay clause (output direction). -/
  delay_post_sep : ∀ t : T, ∀ p ∈ gates, delay.post t p = 0
  /-- Census, plant-immediate clause (input direction). -/
  ipre_sep : ∀ u : Upl, ∀ p ∈ gates, ipre u p = 0
  /-- Census, plant-immediate clause (output direction). -/
  ipost_sep : ∀ u : Upl, ∀ p ∈ gates, ipost u p = 0

/-- **An occupant of the policy seat**: the update-arc data of a
jump-only policy, with confinement carried as fields — every arc of
every update lives on a gate place (the policy acts through
enablement only; its information channels live at the observation
and event strata, not on arcs). -/
structure Occupant {P T Upl : Type} [Fintype P] [DecidableEq P]
    {B : ℕ} (pl : GatePlant P T Upl B) (Upo : Type) where
  /-- Ordinary input arcs of the policy's updates (drains). -/
  upre : Upo → P → ℕ
  /-- Enabling arcs of the policy's updates (wake guards, at this
  uncoloured stratum). -/
  uread : Upo → P → ℕ
  /-- Ordinary output arcs of the policy's updates (mints). -/
  upost : Upo → P → ℕ
  /-- Confinement, input direction. -/
  confine_pre : ∀ u : Upo, ∀ p : P, p ∉ pl.gates → upre u p = 0
  /-- Confinement, enabling direction. -/
  confine_read : ∀ u : Upo, ∀ p : P, p ∉ pl.gates → uread u p = 0
  /-- Confinement, output direction. -/
  confine_post : ∀ u : Upo, ∀ p : P, p ∉ pl.gates → upost u p = 0

/-- **The expansion**: juxtapose plant and occupant into an ordinary
net of the fragment — the enabling-arc reduction as a function.
Places were shared all along (the gate roster is a subset of `P`);
the immediate index splits as plant ⊕ policy. -/
def assemble (pl : GatePlant P T Upl B) (oc : Occupant pl Upo) :
    FinISPN P T (Upl ⊕ Upo) B where
  delay := pl.delay
  ipre := Sum.elim pl.ipre oc.upre
  iread := Sum.elim pl.iread oc.uread
  ipost := Sum.elim pl.ipost oc.upost

/-- The update roster of the expansion: the policy summand. -/
def updRoster (Upl Upo : Type) [Fintype Upl] [Fintype Upo] :
    Finset (Upl ⊕ Upo) :=
  univ.filter fun u => u.isRight

theorem mem_updRoster_inr (u : Upo) :
    (Sum.inr u : Upl ⊕ Upo) ∈ updRoster Upl Upo :=
  mem_filter.mpr ⟨mem_univ _, rfl⟩

theorem not_mem_updRoster_inl (u : Upl) :
    (Sum.inl u : Upl ⊕ Upo) ∉ updRoster Upl Upo := fun h =>
  Bool.false_ne_true (mem_filter.mp h).2

omit [Fintype T] in
/-- **The package-expansion lemma**: every expansion passes the
arc-separation census — the admission check of the two-door
structure, discharged once for the package door (raw rows keep the
census as their own admission check, unchanged). -/
theorem assemble_arcSeparation (pl : GatePlant P T Upl B)
    (oc : Occupant pl Upo) :
    ArcSeparation (assemble pl oc) pl.gates (updRoster Upl Upo) := by
  refine ⟨fun t p hp => ⟨pl.delay_pre_sep t p hp,
    pl.delay_post_sep t p hp⟩, ?_, ?_⟩
  · intro u hu p hp
    cases u with
    | inl v => exact ⟨pl.ipre_sep v p hp, pl.ipost_sep v p hp⟩
    | inr v => exact absurd (mem_updRoster_inr v) hu
  · intro u hu p hp
    cases u with
    | inl v => exact absurd hu (not_mem_updRoster_inl v)
    | inr v => exact ⟨oc.confine_pre v p hp, oc.confine_read v p hp,
        oc.confine_post v p hp⟩

/-! ## The fixed-policy square, collapsed (rung 3)

Deliberately one-line, and the line is the theorem: the supervised
composite is a net of the fragment, so compile-close-close-denote
against interpret-then-include is the landed cascade square *at* the
expansion — no supervision-specific vertical exists to build.
(`gnet₂_supervised_adequacy` is the landed micro-instance; these are
the same collapse at package generality.) -/

/-- **Fixed-policy adequacy of the supervised composite**: the
cascade square applied to the expansion. -/
theorem fixed_policy_adequacy (pl : GatePlant P T Upl B)
    (oc : Occupant pl Upo)
    (σ : Policy (assemble pl oc).Vanishing (Upl ⊕ Upo))
    (r : (assemble pl oc).Vanishing → ℕ)
    (hr : ZenoFree ((assemble pl oc).toFinMA.imStep σ) r) (k : ℕ)
    {a : Crd (Traj (assemble pl oc).Tangible k)} :
    ∃ α : Cell
        (looseConj (atoms (jumpRows
          (closeMaRows (assemble pl oc).compileIspn
            (compilePolicy σ) (absFuel r))) k) : Loose a a)
        (singletonC ((assemble pl oc).tangiblePathLaw σ r hr k))
        (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  (assemble pl oc).ispn_cascade_adequacy σ r hr k

/-- The fixed-policy square, wired to the semantic universe: the
ideal point of a law models the expansion's compiled presentation
exactly when the law is the supervised composite's tangible path
law. -/
theorem su_fixed_policy_adequacy (pl : GatePlant P T Upl B)
    (oc : Occupant pl Upo)
    (σ : Policy (assemble pl oc).Vanishing (Upl ⊕ Upo))
    (r : (assemble pl oc).Vanishing → ℕ)
    (hr : ZenoFree ((assemble pl oc).toFinMA.imStep σ) r) (k : ℕ)
    (μ : SubPMF (Traj (assemble pl oc).Tangible k)) :
    idealPoint μ ∈ ((assemble pl oc).ispnDnf σ r k).modelClass
      ↔ μ = (assemble pl oc).tangiblePathLaw σ r hr k :=
  (assemble pl oc).su_ispn_cascade_adequacy σ r hr k μ

/-! ## The certified seat (rung 4) -/

/-- **A certified occupant of the policy seat**: an occupant together
with a scheduler and a Zeno-freedom certificate for the closed loop —
the `CertScheduler` pattern one level up, which is the honest grain
here because no branch-level certificate can be uniform across the
seat (one occupant's mint and another's drain traverse the same pair
of markings in opposite directions, so a single rank would have to
descend both ways).  The policy's state-space size is genuinely part
of the adversary's choice, so the update index type is bundled. -/
structure CertOccupant {P T Upl : Type} [Fintype P] [DecidableEq P]
    [Fintype T] [Fintype Upl] {B : ℕ} (pl : GatePlant P T Upl B) :
    Type 1 where
  /-- The policy's update index type. -/
  Upo : Type
  /-- Finiteness of the update index. -/
  [fintypeUpo : Fintype Upo]
  /-- The occupant: the policy's update arcs, confined to the
  gates. -/
  occupant : Occupant pl Upo
  /-- The declared scheduler of the closed loop's cascades. -/
  scheduler : Policy (assemble pl occupant).Vanishing (Upl ⊕ Upo)
  /-- The member's own termination rank. -/
  rank : (assemble pl occupant).Vanishing → ℕ
  /-- The member's own Zeno-freedom certificate. -/
  zenoFree : ZenoFree
    ((assemble pl occupant).toFinMA.imStep scheduler) rank

attribute [instance] CertOccupant.fintypeUpo

variable {pl : GatePlant P T Upl B}

/-- **The member constructor from a net rank** — the landed donor,
packaged: one `CascadeRank` on an occupant's composite certifies
every enabling-respecting scheduler at once
(`zenoFree_of_cascadeRank`), so each such pair is a seat member. -/
def CertOccupant.ofCascadeRank (oc : Occupant pl Upo)
    (σ : Policy (assemble pl oc).Vanishing (Upl ⊕ Upo))
    (hσ : (assemble pl oc).RespectsEnabling σ)
    (r : (assemble pl oc).Vanishing → ℕ)
    (hr : (assemble pl oc).CascadeRank r) : CertOccupant pl :=
  { Upo := Upo, occupant := oc, scheduler := σ, rank := r,
    zenoFree := (assemble pl oc).zenoFree_of_cascadeRank σ hσ hr }

/-- The uniform-scheduler member: the community's conflict
resolution, seated. -/
noncomputable def CertOccupant.uniform (oc : Occupant pl Upo)
    (r : (assemble pl oc).Vanishing → ℕ)
    (hr : (assemble pl oc).CascadeRank r) : CertOccupant pl :=
  CertOccupant.ofCascadeRank oc (assemble pl oc).uniformPolicy
    (assemble pl oc).uniformPolicy_respects r hr

/-- **The closed-loop law of a seat member**, on the common marking
space: the tangible path law of the member's composite, pushed
forward along the tangible inclusion at the trajectory level.  The
common carrier is what lets laws of different occupants — whose
tangible/vanishing splits genuinely differ — inhabit one envelope. -/
noncomputable def CertOccupant.law (w : CertOccupant pl) (k : ℕ) :
    SubPMF (Traj (BMarking P B) k) :=
  SubPMF.map (fun ω i => (ω i).1)
    ((assemble pl w.occupant).tangiblePathLaw
      w.scheduler w.rank w.zenoFree k)

/-- Every member's law has full mass — the pushforward preserves the
path law's mass, and the equal-mass slice reconciliation below
spends exactly this. -/
theorem CertOccupant.law_mass (w : CertOccupant pl) (k : ℕ) :
    (w.law k).mass = 1 := by
  unfold CertOccupant.law
  rw [SubPMF.map_mass]
  exact (assemble pl w.occupant).toFinMA.pathLaw_mass
    w.scheduler w.rank w.zenoFree k

/-- **The certificate witnesses; the law is the member's**: two
members differing only in their rank have the same closed-loop law —
inherited from the automaton face's rank-irrelevance through the
pushforward. -/
theorem CertOccupant.law_rank_irrel (oc : Occupant pl Upo)
    (σ : Policy (assemble pl oc).Vanishing (Upl ⊕ Upo))
    {r r' : (assemble pl oc).Vanishing → ℕ}
    (hr : ZenoFree ((assemble pl oc).toFinMA.imStep σ) r)
    (hr' : ZenoFree ((assemble pl oc).toFinMA.imStep σ) r') (k : ℕ) :
    ({ Upo := Upo, occupant := oc, scheduler := σ, rank := r,
       zenoFree := hr } : CertOccupant pl).law k
      = ({ Upo := Upo, occupant := oc, scheduler := σ, rank := r',
           zenoFree := hr' } : CertOccupant pl).law k :=
  congrArg (SubPMF.map _)
    ((assemble pl oc).toFinMA.pathLaw_rank_irrel σ hr hr' k)

/-! ## The demonic gate-envelope -/

/-- **The demonic semantics of the policy seat**, per jump horizon:
the set of closed-loop laws over every certified occupant — the
union of singletons, `EnvelopeUnion` over the seat at its second
genuinely dependent index. -/
def GatePlant.demonicLaws (pl : GatePlant P T Upl B) (k : ℕ) :
    SubPMF (Traj (BMarking P B) k) → Prop :=
  unionSingletons fun w : CertOccupant pl => w.law k

/-- The credal presentation of the gate-envelope: the union of the
members' rays. -/
def GatePlant.demonicCredal (pl : GatePlant P T Upl B) (k : ℕ) :
    SubPMF (Traj (BMarking P B) k) → Prop :=
  unionRays fun w : CertOccupant pl => w.law k

/-- **G-mono, envelope face — containment**: every well-formed
policy's closed-loop law is a member of the gate-envelope.  The
union's defining property, stated as the theorem the safety-transport
story hangs on. -/
theorem CertOccupant.law_mem_demonicLaws (w : CertOccupant pl)
    (k : ℕ) : pl.demonicLaws k (w.law k) :=
  ⟨w, rfl⟩

/-- **The demonic slice**: the radially maximal slice of the credal
gate-envelope is exactly the law-set — the equal-mass reconciliation
at `m = 1`, every member's law having full mass. -/
theorem demonic_maxSlice (pl : GatePlant P T Upl B) (k : ℕ)
    (ν : SubPMF (Traj (BMarking P B) k)) :
    maxSlice (pl.demonicCredal k) ν ↔ pl.demonicLaws k ν :=
  maxSlice_unionRays (fun w => w.law_mass k) one_ne_zero ν

/-! ### The verdicts: certify once against the gate-demon -/

/-- **The lower verdict is the uniform-over-the-seat bound**: a
lower-kind constraint holds of the credal gate-envelope exactly when
it holds of every certified occupant's closed-loop law — safety
certified once against the gate-demon transports to every
partially-sighted policy. -/
theorem satCredal_lower_demonicCredal (pl : GatePlant P T Upl B)
    (k : ℕ) (c : SubPMF (Traj (BMarking P B) k) → Prop) :
    SatCredal .lower (pl.demonicCredal k) c ↔
      ∀ w : CertOccupant pl, c (w.law k) :=
  satCredal_lower_unionRays (fun w => w.law_mass k) one_ne_zero c

/-- The upper verdict on the credal gate-envelope, for down-closed
constraints — mass-free, through down-closure. -/
theorem satCredal_upper_demonicCredal (pl : GatePlant P T Upl B)
    (k : ℕ) {c : SubPMF (Traj (BMarking P B) k) → Prop}
    (hc : DownClosed c) :
    SatCredal .upper (pl.demonicCredal k) c ↔
      ∀ w : CertOccupant pl, c (w.law k) :=
  satCredal_upper_unionRays hc

theorem satCredal_lower_demonicLaws (pl : GatePlant P T Upl B)
    (k : ℕ) (c : SubPMF (Traj (BMarking P B) k) → Prop) :
    SatCredal .lower (pl.demonicLaws k) c ↔
      ∀ w : CertOccupant pl, c (w.law k) :=
  satCredal_lower_unionSingletons (fun w => w.law_mass k)
    one_ne_zero c

theorem satCredal_upper_demonicLaws (pl : GatePlant P T Upl B)
    (k : ℕ) (c : SubPMF (Traj (BMarking P B) k) → Prop) :
    SatCredal .upper (pl.demonicLaws k) c ↔
      ∀ w : CertOccupant pl, c (w.law k) :=
  satCredal_upper_unionSingletons c

/-- Verdict agreement, lower kind: the credal and exact presentations
of the gate-envelope agree on every lower-kind constraint. -/
theorem satCredal_lower_demonic_ray_singleton
    (pl : GatePlant P T Upl B) (k : ℕ)
    (c : SubPMF (Traj (BMarking P B) k) → Prop) :
    SatCredal .lower (pl.demonicCredal k) c ↔
      SatCredal .lower (pl.demonicLaws k) c := by
  rw [satCredal_lower_demonicCredal pl k,
    satCredal_lower_demonicLaws pl k]

/-- Verdict agreement, upper kind: for down-closed constraints. -/
theorem satCredal_upper_demonic_ray_singleton
    (pl : GatePlant P T Upl B) (k : ℕ)
    {c : SubPMF (Traj (BMarking P B) k) → Prop} (hc : DownClosed c) :
    SatCredal .upper (pl.demonicCredal k) c ↔
      SatCredal .upper (pl.demonicLaws k) c := by
  rw [satCredal_upper_demonicCredal pl k hc,
    satCredal_upper_demonicLaws pl k]

/-! ### Roster monotonicity: fewer gates ⊆ more gates -/

/-- Widen a plant's gate roster: same plant data, more places handed
to the policy seat — with the plant-side census at the new roster
supplied (a plant transition with ordinary arcs at a newly-gated
place would be exactly what the census refuses; the hypotheses are
the honest price of the widening). -/
def GatePlant.widen (pl : GatePlant P T Upl B) (gates' : Finset P)
    (hd1 : ∀ t : T, ∀ p ∈ gates', pl.delay.pre t p = 0)
    (hd2 : ∀ t : T, ∀ p ∈ gates', pl.delay.post t p = 0)
    (hi1 : ∀ u : Upl, ∀ p ∈ gates', pl.ipre u p = 0)
    (hi2 : ∀ u : Upl, ∀ p ∈ gates', pl.ipost u p = 0) :
    GatePlant P T Upl B where
  -- Explicit-field construction, deliberately NOT `{ pl with … }`:
  -- a structure update on a dependent structure compiles to a
  -- `casesOn` of the variable, which reduces nothing — and the whole
  -- monotonicity transport below rides on the widened plant's fields
  -- being *definitionally* the original's.
  delay := pl.delay
  ipre := pl.ipre
  iread := pl.iread
  ipost := pl.ipost
  gates := gates'
  delay_pre_sep := hd1
  delay_post_sep := hd2
  ipre_sep := hi1
  ipost_sep := hi2

/-- An occupant survives roster widening: confinement only weakens
as the roster grows. -/
def Occupant.widen (oc : Occupant pl Upo) {gates' : Finset P}
    (hsub : pl.gates ⊆ gates')
    (hd1 : ∀ t : T, ∀ p ∈ gates', pl.delay.pre t p = 0)
    (hd2 : ∀ t : T, ∀ p ∈ gates', pl.delay.post t p = 0)
    (hi1 : ∀ u : Upl, ∀ p ∈ gates', pl.ipre u p = 0)
    (hi2 : ∀ u : Upl, ∀ p ∈ gates', pl.ipost u p = 0) :
    Occupant (pl.widen gates' hd1 hd2 hi1 hi2) Upo where
  upre := oc.upre
  uread := oc.uread
  upost := oc.upost
  confine_pre u p hp := oc.confine_pre u p fun hm => hp (hsub hm)
  confine_read u p hp := oc.confine_read u p fun hm => hp (hsub hm)
  confine_post u p hp := oc.confine_post u p fun hm => hp (hsub hm)

omit [Fintype T] [Fintype Upl] [Fintype Upo] in
/-- **The widening changes nothing about the net** — definitionally:
the expansion of the widened pair is the expansion of the original
pair, `rfl`.  (The roster is census data, not wiring data; this is
the pin that makes the monotonicity transport silent.) -/
theorem assemble_widen (oc : Occupant pl Upo) {gates' : Finset P}
    (hsub : pl.gates ⊆ gates')
    (hd1 : ∀ t : T, ∀ p ∈ gates', pl.delay.pre t p = 0)
    (hd2 : ∀ t : T, ∀ p ∈ gates', pl.delay.post t p = 0)
    (hi1 : ∀ u : Upl, ∀ p ∈ gates', pl.ipre u p = 0)
    (hi2 : ∀ u : Upl, ∀ p ∈ gates', pl.ipost u p = 0) :
    assemble (pl.widen gates' hd1 hd2 hi1 hi2)
      (oc.widen hsub hd1 hd2 hi1 hi2) = assemble pl oc :=
  rfl

/-- A certified occupant survives roster widening: the closed loop
is the same net, so the scheduler, rank, and certificate carry over
unchanged. -/
def CertOccupant.widen (w : CertOccupant pl) {gates' : Finset P}
    (hsub : pl.gates ⊆ gates')
    (hd1 : ∀ t : T, ∀ p ∈ gates', pl.delay.pre t p = 0)
    (hd2 : ∀ t : T, ∀ p ∈ gates', pl.delay.post t p = 0)
    (hi1 : ∀ u : Upl, ∀ p ∈ gates', pl.ipre u p = 0)
    (hi2 : ∀ u : Upl, ∀ p ∈ gates', pl.ipost u p = 0) :
    CertOccupant (pl.widen gates' hd1 hd2 hi1 hi2) :=
  { Upo := w.Upo, occupant := w.occupant.widen hsub hd1 hd2 hi1 hi2,
    scheduler := w.scheduler, rank := w.rank, zenoFree := w.zenoFree }

/-- **G-mono, envelope face — roster monotonicity**: the
gate-envelope only grows as the roster does.  Fewer gates ⊆ more
gates ⊆ the full relaxation: handing the seat more places can only
enlarge the family of closed loops, so any verdict certified against
the wider envelope transports to the narrower one for free — the
family-level face of the landed `enabled_mono` statics. -/
theorem GatePlant.demonicLaws_mono_gates (pl : GatePlant P T Upl B)
    {gates' : Finset P} (hsub : pl.gates ⊆ gates')
    (hd1 : ∀ t : T, ∀ p ∈ gates', pl.delay.pre t p = 0)
    (hd2 : ∀ t : T, ∀ p ∈ gates', pl.delay.post t p = 0)
    (hi1 : ∀ u : Upl, ∀ p ∈ gates', pl.ipre u p = 0)
    (hi2 : ∀ u : Upl, ∀ p ∈ gates', pl.ipost u p = 0) (k : ℕ)
    (ν : SubPMF (Traj (BMarking P B) k)) :
    pl.demonicLaws k ν →
      (pl.widen gates' hd1 hd2 hi1 hi2).demonicLaws k ν := by
  rintro ⟨w, hw⟩
  exact ⟨w.widen hsub hd1 hd2 hi1 hi2, hw⟩

/-- Roster monotonicity, credal presentation. -/
theorem GatePlant.demonicCredal_mono_gates (pl : GatePlant P T Upl B)
    {gates' : Finset P} (hsub : pl.gates ⊆ gates')
    (hd1 : ∀ t : T, ∀ p ∈ gates', pl.delay.pre t p = 0)
    (hd2 : ∀ t : T, ∀ p ∈ gates', pl.delay.post t p = 0)
    (hi1 : ∀ u : Upl, ∀ p ∈ gates', pl.ipre u p = 0)
    (hi2 : ∀ u : Upl, ∀ p ∈ gates', pl.ipost u p = 0) (k : ℕ)
    (ν : SubPMF (Traj (BMarking P B) k)) :
    pl.demonicCredal k ν →
      (pl.widen gates' hd1 hd2 hi1 hi2).demonicCredal k ν := by
  rintro ⟨w, hw⟩
  exact ⟨w.widen hsub hd1 hd2 hi1 hi2, hw⟩

/-! ### Degeneracies, mechanized -/

/-- **The empty policy**: the occupant with no updates at all —
trivially confined, trivially well-formed.  Deliberate idling as a
seat inhabitant. -/
def GatePlant.idleOccupant (pl : GatePlant P T Upl B) :
    Occupant pl Empty where
  upre := fun u => u.elim
  uread := fun u => u.elim
  upost := fun u => u.elim
  confine_pre := fun u => u.elim
  confine_read := fun u => u.elim
  confine_post := fun u => u.elim

/-- **Deliberate idling is a member**: given a rank for the plant's
own cascades, the empty policy's closed-loop law is in the
gate-envelope.  This is the family-level root of the polarity
finding: no liveness claim survives the ∀-over-members reading
wherever a gated transition is load-bearing, because the occupant
that never mints is inside the union (`gnet₃_idles` pins the
specimen: under the empty policy a gate-closed marking is tangible
and inert). -/
theorem GatePlant.idle_mem_demonicLaws (pl : GatePlant P T Upl B)
    (r : (assemble pl pl.idleOccupant).Vanishing → ℕ)
    (hr : (assemble pl pl.idleOccupant).CascadeRank r) (k : ℕ) :
    pl.demonicLaws k ((CertOccupant.uniform pl.idleOccupant r hr).law k) :=
  (CertOccupant.uniform pl.idleOccupant r hr).law_mem_demonicLaws k

/-- A plant rank makes the seat nonempty — the route every concrete
model takes (the idle member exists as soon as the plant's own
cascades terminate). -/
theorem GatePlant.certOccupant_nonempty (pl : GatePlant P T Upl B)
    (r : (assemble pl pl.idleOccupant).Vanishing → ℕ)
    (hr : (assemble pl pl.idleOccupant).CascadeRank r) :
    Nonempty (CertOccupant pl) :=
  ⟨CertOccupant.uniform pl.idleOccupant r hr⟩

/-- **The slice discipline survives the passage to the seat**: as
soon as one member exists, the credal gate-envelope contains the
zero model, so the whole-set reading of a lower-bound atom refuses
every positive threshold — the reconciliation must route lower-kind
verdicts through the slice, exactly as at the automaton face. -/
theorem not_satCredal_upper_demonicCredal_geC
    (pl : GatePlant P T Upl B) (k : ℕ)
    [hp : Nonempty (CertOccupant pl)]
    {E : Set (Traj (BMarking P B) k)} {q : ℚ} (hq : 0 < q) :
    ¬ SatCredal .upper (pl.demonicCredal k) (geC E q) := by
  intro h
  obtain ⟨w⟩ := hp
  have h0 : q ≤ (SubPMF.zero (Traj (BMarking P B) k)).prob E :=
    h (SubPMF.zero _) ⟨w, rayC_zero _⟩
  rw [SubPMF.zero_prob] at h0
  linarith

/-- **The empty seat validates everything**: with no certified
occupants, both verdict kinds pass vacuously — the
∀-over-no-adversaries convention, recorded rather than smoothed,
exactly as at the automaton and decision faces. -/
theorem satCredal_demonic_of_isEmpty_certOccupant
    (pl : GatePlant P T Upl B) (k : ℕ)
    [h : IsEmpty (CertOccupant pl)] (kind : EnvelopeKind)
    (c : SubPMF (Traj (BMarking P B) k) → Prop) :
    SatCredal kind (pl.demonicCredal k) c := by
  cases kind with
  | lower =>
    rintro ν ⟨⟨w, -⟩, -⟩
    exact (h.false w).elim
  | upper =>
    rintro ν ⟨w, -⟩
    exact (h.false w).elim

end Supervise

/-! ## Controls

The seat pipeline end-to-end on the mini plant — the `gnet₂`
decomposition *as package data*: queue + gate, one gated plant
dispatch, one mint occupant.  Census by both the expansion lemma and
independent decision (the designed mutant locus for the `Sum.elim`
wiring); a cascade rank by decision; the uniform member assembled;
membership and mass consumed as stated. -/

namespace SuperviseDemonicControls

open FinISPN Supervise SpnCascadeControls

/-- The mini plant: place 0 the queue, place 1 the gate; one inert
delay row carrying the initial distribution; one plant immediate —
the gated dispatch (consume a queue token, read the gate). -/
def plG : GatePlant (Fin 2) (Fin 1) (Fin 1) 1 where
  delay :=
    { pre := fun _ _ => 0
      read := fun _ _ => 0
      post := fun _ _ => 0
      rate := fun _ => 0
      rate_nonneg := fun _ => le_rfl
      init := fun m => if m = m10 then 1 else 0
      init_nonneg := fun m => by by_cases h : m = m10 <;> simp [h]
      init_sum := Finset.sum_ite_eq' _ _ _ |>.trans
        (if_pos (Finset.mem_univ _)) }
  ipre := fun _ p => if p = 0 then 1 else 0
  iread := fun _ p => if p = 1 then 1 else 0
  ipost := fun _ _ => 0
  gates := {1}
  delay_pre_sep := by decide
  delay_post_sep := by decide
  ipre_sep := by decide
  ipost_sep := by decide

/-- The mint occupant: one update, producing a gate token. -/
def ocMint : Occupant plG (Fin 1) where
  upre := fun _ _ => 0
  uread := fun _ _ => 0
  upost := fun _ p => if p = 1 then 1 else 0
  confine_pre := by decide
  confine_read := by decide
  confine_post := by decide

/-- The expansion's wiring, pinned (mutant locus: swapped `Sum.elim`
arms): the plant's dispatch consumes the queue… -/
theorem plG_wiring_dispatch_pre :
    (assemble plG ocMint).ipre (Sum.inl 0) 0 = 1 := by decide

/-- …and reads the gate… -/
theorem plG_wiring_dispatch_read :
    (assemble plG ocMint).iread (Sum.inl 0) 1 = 1 := by decide

/-- …while the policy's mint produces into the gate place. -/
theorem plG_wiring_mint_post :
    (assemble plG ocMint).ipost (Sum.inr 0) 1 = 1 := by decide

/-- The census on the expansion, by independent decision — the
second witness beside `assemble_arcSeparation` (which discharges it
by construction; proofs deliberately independent). -/
theorem plG_census :
    ArcSeparation (assemble plG ocMint)
      plG.gates (updRoster (Fin 1) (Fin 1)) := by decide

/-- The same census, from the expansion lemma. -/
theorem plG_census' :
    ArcSeparation (assemble plG ocMint)
      plG.gates (updRoster (Fin 1) (Fin 1)) :=
  assemble_arcSeparation plG ocMint

/-! ### The supervised mini composite, classified

`netG` is `gnet₂` rebuilt as package data (the immediate index is now
`Fin 1 ⊕ Fin 1`: plant dispatch ⊕ policy mint).  Rank proofs follow
the cascade module's manual pattern — enumeration plus per-case
computation — because a raw `decide` on `CascadeRank` reduces through
equality on the sum-of-subtypes state space, whose `Decidable`
instance sticks on an `Eq.rec` (the same reason the landed module
proved `gnet₂_rank` by hand). -/

/-- The supervised mini composite. -/
abbrev netG : FinISPN (Fin 2) (Fin 1) (Fin 1 ⊕ Fin 1) 1 :=
  assemble plG ocMint

theorem netG_m01_tangible : ¬ netG.IsVanishing m01 := by
  rintro ⟨u | u, h⟩
  · exact (by decide : ∀ v : Fin 1,
      ¬ netG.IEnabled (Sum.inl v) m01) u h
  · exact (by decide : ∀ v : Fin 1,
      ¬ netG.IEnabled (Sum.inr v) m01) u h

/-- The classified elements of `netG`, named for the controls. -/
def tG : netG.Tangible := ⟨m01, netG_m01_tangible⟩
def vG00 : netG.Vanishing := ⟨m00, ⟨Sum.inr 0, by decide⟩⟩
def vG10 : netG.Vanishing := ⟨m10, ⟨Sum.inr 0, by decide⟩⟩
def vG11 : netG.Vanishing := ⟨m11, ⟨Sum.inl 0, by decide⟩⟩

theorem netG_vanishing_univ :
    (Finset.univ : Finset netG.Vanishing) = {vG00, vG10, vG11} := by
  decide

/-- The idle wake: minting at an empty queue absorbs immediately. -/
theorem netG_fire_idle_mint :
    netG.toSum (netG.ifire (Sum.inr 0) vG00.1) = Sum.inl tG := by
  rw [show netG.ifire (Sum.inr 0) vG00.1 = m01 from by decide]
  exact dif_neg netG_m01_tangible

/-- The wake at a waiting queue: still vanishing (the dispatch is now
enabled) — the cascade genuinely passes through the policy's own
update. -/
theorem netG_fire_mint :
    netG.toSum (netG.ifire (Sum.inr 0) vG10.1) = Sum.inr vG11 := by
  rw [show netG.ifire (Sum.inr 0) vG10.1 = m11 from by decide]
  exact dif_pos vG11.2

/-- The dispatch: queue served, gate token retained
(read-no-consume) — tangible. -/
theorem netG_fire_dispatch :
    netG.toSum (netG.ifire (Sum.inl 0) vG11.1) = Sum.inl tG := by
  rw [show netG.ifire (Sum.inl 0) vG11.1 = m01 from by decide]
  exact dif_neg netG_m01_tangible

/-- The mini composite's cascade rank: queue tokens waiting at a
closed gate (`gnet₂`'s rank shape, at the package's expansion). -/
def rG : netG.Vanishing → ℕ :=
  fun i => (i.1 0 : ℕ) * (1 - (i.1 1 : ℕ))

theorem netG_rank : netG.CascadeRank rG := by
  intro i u hu j hj
  have hi : i = vG00 ∨ i = vG10 ∨ i = vG11 := by
    have h := Finset.mem_univ i
    rw [netG_vanishing_univ] at h
    simpa using h
  rcases hi with rfl | rfl | rfl
  · obtain rfl : u = Sum.inr 0 :=
      (by decide : ∀ v : Fin 1 ⊕ Fin 1,
        netG.IEnabled v vG00.1 → v = Sum.inr 0) u hu
    rw [netG_fire_idle_mint] at hj
    simp at hj
  · obtain rfl : u = Sum.inr 0 :=
      (by decide : ∀ v : Fin 1 ⊕ Fin 1,
        netG.IEnabled v vG10.1 → v = Sum.inr 0) u hu
    rw [netG_fire_mint] at hj
    obtain rfl : vG11 = j := by simpa using hj
    decide
  · obtain rfl : u = Sum.inl 0 :=
      (by decide : ∀ v : Fin 1 ⊕ Fin 1,
        netG.IEnabled v vG11.1 → v = Sum.inl 0) u hu
    rw [netG_fire_dispatch] at hj
    simp at hj

/-- The uniform member of the mini plant's seat. -/
noncomputable def wG : CertOccupant plG :=
  CertOccupant.uniform ocMint rG netG_rank

/-- The member's law is in the envelope — containment consumed as
stated. -/
theorem wG_mem (k : ℕ) : plG.demonicLaws k (wG.law k) :=
  wG.law_mem_demonicLaws k

/-- The member's law has full mass — the pushforward preserved the
path law's mass (mutant locus: a mass-dropping `map`). -/
theorem wG_mass (k : ℕ) : (wG.law k).mass = 1 :=
  wG.law_mass k

/-! ### The idle composite: the empty policy, seated -/

/-- The plant under the empty policy. -/
abbrev netI : FinISPN (Fin 2) (Fin 1) (Fin 1 ⊕ Empty) 1 :=
  assemble plG plG.idleOccupant

theorem netI_m01_tangible : ¬ netI.IsVanishing m01 := by
  rintro ⟨u | u, h⟩
  · exact (by decide : ∀ v : Fin 1,
      ¬ netI.IEnabled (Sum.inl v) m01) u h
  · exact u.elim

/-- Under the empty policy the queue-waiting marking is tangible —
the gated dispatch is blocked and nothing will ever open the gate
(the `gnet₃_idles` specimen, at the package's expansion). -/
theorem netI_m10_tangible : ¬ netI.IsVanishing m10 := by
  rintro ⟨u | u, h⟩
  · exact (by decide : ∀ v : Fin 1,
      ¬ netI.IEnabled (Sum.inl v) m10) u h
  · exact u.elim

def tI : netI.Tangible := ⟨m01, netI_m01_tangible⟩
def vI11 : netI.Vanishing := ⟨m11, ⟨Sum.inl 0, by decide⟩⟩

theorem netI_vanishing_univ :
    (Finset.univ : Finset netI.Vanishing) = {vI11} := by decide

theorem netI_fire_dispatch :
    netI.toSum (netI.ifire (Sum.inl 0) vI11.1) = Sum.inl tI := by
  rw [show netI.ifire (Sum.inl 0) vI11.1 = m01 from by decide]
  exact dif_neg netI_m01_tangible

/-- The idle composite's cascade rank is trivial: the only immediate
is the plant's dispatch, and its firing lands tangible. -/
def rIdle : netI.Vanishing → ℕ := fun _ => 0

theorem netI_rank : netI.CascadeRank rIdle := by
  intro i u hu j hj
  have hi : i = vI11 := by
    have h := Finset.mem_univ i
    rw [netI_vanishing_univ] at h
    simpa using h
  subst hi
  obtain rfl : u = Sum.inl 0 := by
    rcases u with u | u
    · exact congrArg Sum.inl (Fin.ext (Nat.lt_one_iff.mp u.isLt))
    · exact u.elim
  rw [netI_fire_dispatch] at hj
  simp at hj

/-- Deliberate idling, seated: the empty policy's closed-loop law is
a member of the mini plant's envelope. -/
theorem plG_idle_mem (k : ℕ) :
    plG.demonicLaws k
      ((CertOccupant.uniform plG.idleOccupant rIdle netI_rank).law k) :=
  plG.idle_mem_demonicLaws rIdle netI_rank k

end SuperviseDemonicControls

end Adequacy
end SuFunctor
