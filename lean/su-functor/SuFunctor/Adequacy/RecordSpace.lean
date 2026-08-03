import SuFunctor.Adequacy.SemanticUniverseWiring

/-! # Record spaces of the compiled systems: the wire objects

The wiring layer ties each adequacy square to the semantic universe
per-carrier: its statements live over the fibre carrier
`SpecDnf (Joint V)` with the record space `V` supplied directly — the
fibre of the semantic universe over *any* wire object whose state
space is `V` — and the construction of that wire object was left as a
separate, named stratum.  This module is that stratum, at the squares'
altitude.  (The checker-carrier module built the same stratum at
verdict altitude, for the certificate calculus's sequents; the two
constructions share the base and the design, not their stock.)

Two wire objects do all the work.

* **The trajectory interface** (`trajWire`): horizon-`k` trajectories
  are assignments of a state to each of `k + 1` record slots, so the
  interface whose wires are the slots has the trajectory space as its
  state space *definitionally* — the wired chain and decision-process
  statements re-instantiate by substitution, as citizens of the fibre
  over `trajWire S k`.  Record structure rides along: horizon
  inclusions are tight arrows of the wiring base, and restriction
  along them is prefix-reading.

* **The assignment interface** (`asnWire`): joint assignments of a
  graphical model are *dependent* functions, not states of any
  interface over a single stock, so the identification is the erasure
  pattern one level up — states over the sigma stock, with
  wellformedness as the guard: assignments are exactly the well-typed
  states (`range_asnState`).  The compiled network's presentation
  transports along the embedding *within the wiring's own genre*, by
  pushforward of laws (`SubPMF.map`) and of per-element constraints
  (`cmap`); the transported adequacy runs through the same generic
  judgment bridge as the intrinsic one, and nothing is re-proved.

The slice corollaries for the trajectory carriers coincide with their
intrinsic forms definitionally and are re-typed below; no slice
reading is duplicated at the assignment interface, because slice
discipline is a verdict-layer operation over the intrinsic law space
and the transported judgment consumes the intrinsic reconciliation
unchanged. -/

namespace SuFunctor

open CategoryTheory CategoryTheory.WireSpan

open scoped NNReal ENNReal

universe u

/-! ## Pushforward of laws along a carrier map -/

namespace SubPMF

variable {X Y : Type u}

/-- Pushforward of a law along a map of carriers: relabel the
outcomes, summing weights over fibres. -/
noncomputable def map (f : X → Y) (μ : SubPMF X) : SubPMF Y where
  wt := μ.wt.mapDomain f
  nonneg := by
    classical
    intro y
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    refine Finset.sum_nonneg fun a _ => ?_
    simp only [Finsupp.single_apply]
    split
    · exact μ.nonneg a
    · exact le_refl 0
  mass_le_one := by
    classical
    have h : (μ.wt.mapDomain f).sum (fun _ c => c)
        = μ.wt.sum fun _ c => c :=
      Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)
    simp only [Finsupp.sum] at h
    rw [h]
    exact μ.mass_le_one

@[simp] theorem map_wt (f : X → Y) (μ : SubPMF X) :
    (μ.map f).wt = μ.wt.mapDomain f :=
  rfl

/-- Pushforward along an injection loses nothing. -/
theorem map_injective {f : X → Y} (hf : Function.Injective f) :
    Function.Injective (map f) := by
  intro μ ν h
  exact SubPMF.ext'
    (Finsupp.mapDomain_injective hf (congrArg SubPMF.wt h))

end SubPMF

namespace Adequacy

open SuFunctor.Universe (CoupledSat SpecAtom SpecDnf)

/-! ## Pushforward of constraints, in the wiring's genre -/

section ConstraintMap

variable {X Y : Type u}

/-- Pushforward of a per-element constraint along a carrier map: the
image constraint, holding exactly at pushforwards of satisfying
laws. -/
def cmap (f : X → Y) (c : SubPMF X → Prop) : SubPMF Y → Prop :=
  fun ν => ∃ μ, c μ ∧ ν = SubPMF.map f μ

/-- Along an injection, the pushed constraint reads back at pushed
laws. -/
theorem cmap_map_iff {f : X → Y} (hf : Function.Injective f)
    {c : SubPMF X → Prop} {μ : SubPMF X} :
    cmap f c (μ.map f) ↔ c μ := by
  constructor
  · rintro ⟨μ', hc, he⟩
    obtain rfl := SubPMF.map_injective hf he
    exact hc
  · intro hc
    exact ⟨μ, hc, rfl⟩

/-- The pushed diagram's conjunction reads back at pushed laws: the
constraint stratum transports clause by clause. -/
theorem looseConj_map {f : X → Y} (hf : Function.Injective f)
    (L : List (SubPMF X → Prop)) (μ : SubPMF X) :
    looseConj (L.map (cmap f)) (μ.map f) ↔ looseConj L μ := by
  induction L with
  | nil => simp [looseConj]
  | cons c L ih => simp [looseConj, cmap_map_iff hf, ih]

/-- **The transported judgment bridge**: along an injection of
carriers, membership of the pushed ideal point in the pushed
presentation's model class is exactly satisfaction of the intrinsic
diagram — the wiring's generic bridge, read at the far carrier. -/
theorem idealPoint_map_mem_diagramDnf_iff {f : X → Y}
    (hf : Function.Injective f) (L : List (SubPMF X → Prop))
    (μ : SubPMF X) :
    idealPoint (μ.map f) ∈ (diagramDnf (L.map (cmap f))).modelClass
      ↔ looseConj L μ :=
  (idealPoint_mem_diagramDnf_iff (L.map (cmap f)) (μ.map f)).trans
    (looseConj_map hf L μ)

end ConstraintMap

/-! ## The trajectory interface -/

section TrajectoryWire

/-- The trajectory interface: one wire per record slot of a
horizon-`k` trajectory. -/
def trajWire (S : Type) (k : ℕ) : WireSpan S :=
  ⟨Fin (k + 1)⟩

/-- Horizon-`k` trajectories are the states of the trajectory
interface — definitionally: the record space of the compiled system,
over the wiring base. -/
theorem states_trajWire (S : Type) (k : ℕ) :
    states (trajWire S k) = Traj S k :=
  rfl

/-- Horizon inclusion as a tight arrow of the wiring base. -/
def trajTight (S : Type) {j k : ℕ} (h : j ≤ k) :
    trajWire S j ⟶ trajWire S k :=
  fun i => Fin.castLE (Nat.succ_le_succ h) i

/-- Restriction along a horizon inclusion is prefix-reading: the
record structure of the trajectory space, carried by the base's tight
calculus. -/
theorem res_trajTight (S : Type) {j k : ℕ} (h : j ≤ k)
    (y : states (trajWire S k)) :
    res (trajTight S h) y
      = fun i => y (Fin.castLE (Nat.succ_le_succ h) i) :=
  rfl

end TrajectoryWire

/-! ## The chain square, in the fibre over its wire object -/

section ChainFibre

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The compiled chain's presentation, as a citizen of the semantic
universe's fibre over the trajectory interface — by type. -/
noncomputable def dtmcSpec (R : DtmcRows S) (k : ℕ) :
    DnfSpec (trajWire S k) :=
  dtmcDnf R k

/-- **The chain square, in the fibre**: the ideal point of a law
models the compiled chain's presentation — read in the semantic
universe's fibre over the trajectory interface — exactly when the law
is the chain's classical path law. -/
theorem su_dtmc_adequacy_fibre (M : FinDTMC S) (k : ℕ)
    (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈ (dtmcSpec (compile M) k).modelClass
      ↔ μ = M.pathLaw k :=
  su_dtmc_adequacy M k μ

/-- The positive face, in the fibre. -/
theorem su_dtmc_pathLaw_mem_fibre (M : FinDTMC S) (k : ℕ) :
    idealPoint (M.pathLaw k) ∈ (dtmcSpec (compile M) k).modelClass :=
  su_dtmc_pathLaw_mem M k

omit [DecidableEq S] in
/-- Ex falso at the chain's corner, in the fibre. -/
theorem su_dtmc_bottom_fibre (M : FinDTMC S) (k : ℕ) :
    (⊤ : Plain.Pen (states (trajWire S k)))
      ∉ (dtmcSpec (compile M) k).modelClass :=
  su_dtmc_bottom M k

/-- The credal reading at the chain's corner, in the fibre. -/
theorem su_dtmc_slice_fibre (M : FinDTMC S) (k : ℕ)
    (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈ (dtmcSpec (compile M) k).modelClass
      ↔ maxSlice (rayC (M.pathLaw k)) μ :=
  su_dtmc_slice M k μ

end ChainFibre

/-! ## The decision-process squares, in the fibre over their wire object -/

section DecisionFibre

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- The compiled decision former's fixed-policy presentation, as a
citizen of the fibre over the trajectory interface — by type. -/
noncomputable def mdpSpec (R : MdpRows S A) (σp : PolicyRows S A)
    (k : ℕ) : DnfSpec (trajWire S k) :=
  mdpDnf R σp k

/-- The compiled decision former's demonic presentation, as a citizen
of the fibre over the trajectory interface — by type. -/
noncomputable def mdpDemonicSpec (R : MdpRows S A) (k : ℕ) :
    DnfSpec (trajWire S k) :=
  mdpDemonicDnf R k

omit [DecidableEq A] in
/-- **The fixed-policy square, in the fibre.** -/
theorem su_mdp_adequacy_fibre (M : FinMDP S A) (π : Policy S A) (k : ℕ)
    (μ : SubPMF (Traj S k)) :
    idealPoint μ
        ∈ (mdpSpec (compileMdp M) (compilePolicy π) k).modelClass
      ↔ μ = M.pathLaw π k :=
  su_mdp_adequacy M π k μ

omit [DecidableEq A] in
/-- The positive face at the fixed-policy corner, in the fibre. -/
theorem su_mdp_pathLaw_mem_fibre (M : FinMDP S A) (π : Policy S A)
    (k : ℕ) :
    idealPoint (M.pathLaw π k)
      ∈ (mdpSpec (compileMdp M) (compilePolicy π) k).modelClass :=
  su_mdp_pathLaw_mem M π k

omit [DecidableEq S] [DecidableEq A] in
/-- Ex falso at the fixed-policy corner, in the fibre. -/
theorem su_mdp_bottom_fibre (M : FinMDP S A) (π : Policy S A) (k : ℕ) :
    (⊤ : Plain.Pen (states (trajWire S k)))
      ∉ (mdpSpec (compileMdp M) (compilePolicy π) k).modelClass :=
  su_mdp_bottom M π k

omit [DecidableEq A] in
/-- The credal reading at the fixed-policy corner, in the fibre. -/
theorem su_mdp_slice_fibre (M : FinMDP S A) (π : Policy S A) (k : ℕ)
    (μ : SubPMF (Traj S k)) :
    idealPoint μ
        ∈ (mdpSpec (compileMdp M) (compilePolicy π) k).modelClass
      ↔ maxSlice (rayC (M.pathLaw π k)) μ :=
  su_mdp_slice M π k μ

/-- **The demonic square, in the fibre — the set stratum.** -/
theorem su_mdp_demonic_fibre (M : FinMDP S A) (k : ℕ)
    (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈ (mdpDemonicSpec (compileMdp M) k).modelClass
      ↔ M.demonicLaws k μ :=
  su_mdp_demonic_wiring M k μ

/-- The policy-explicit face of the demonic square, in the fibre. -/
theorem su_mdp_demonic_fibre' (M : FinMDP S A) (k : ℕ)
    (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈ (mdpDemonicSpec (compileMdp M) k).modelClass
      ↔ ∃ π : Policy S A, μ = M.pathLaw π k :=
  su_mdp_demonic_wiring' M k μ

omit [DecidableEq S] [DecidableEq A] in
/-- Ex falso at the demonic corner, in the fibre. -/
theorem su_mdp_demonic_bottom_fibre (M : FinMDP S A) (k : ℕ) :
    (⊤ : Plain.Pen (states (trajWire S k)))
      ∉ (mdpDemonicSpec (compileMdp M) k).modelClass :=
  su_mdp_demonic_bottom M k

/-- The credal reading at the demonic corner, in the fibre. -/
theorem su_mdp_demonic_slice_fibre (M : FinMDP S A) (k : ℕ)
    (ν : SubPMF (Traj S k)) :
    idealPoint ν ∈ (mdpDemonicSpec (compileMdp M) k).modelClass
      ↔ maxSlice (M.demonicCredal k) ν :=
  su_mdp_demonic_slice M k ν

end DecisionFibre

/-! ## The assignment interface -/

section AssignmentWire

variable {n : ℕ} {Val : Fin (n + 1) → Type}

/-- The state stock of the assignment interface: a vertex together
with a value of its type.  Network-independent across networks on the
same vertex typing. -/
def AsnEl (Val : Fin (n + 1) → Type) : Type :=
  Σ j, Val j

/-- The assignment interface: one wire per vertex, over the sigma
stock. -/
def asnWire (Val : Fin (n + 1) → Type) : WireSpan (AsnEl Val) :=
  ⟨Fin (n + 1)⟩

/-- A joint assignment, read as a state of the assignment
interface. -/
def asnState (a : Pgm.Asn Val) : states (asnWire Val) :=
  fun j => ⟨j, a j⟩

/-- Distinct assignments read as distinct states: the embedding loses
nothing. -/
theorem asnState_injective :
    Function.Injective (asnState (Val := Val)) := by
  intro a b h
  funext j
  have hj : (⟨j, a j⟩ : AsnEl Val) = ⟨j, b j⟩ := congrFun h j
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at hj
  exact hj

/-- Wellformedness of a state of the assignment interface: each
wire's state names that wire's vertex. -/
def AsnWf (s : states (asnWire Val)) : Prop :=
  ∀ j, (s j).1 = j

/-- Reconstruct an assignment from a well-typed state. -/
def asnOfState (s : states (asnWire Val)) (hs : AsnWf s) :
    Pgm.Asn Val := fun j =>
  cast (congrArg Val (hs j)) (s j).2

theorem asnState_asnOfState (s : states (asnWire Val))
    (hs : AsnWf s) : asnState (asnOfState s hs) = s := by
  funext j
  exact Sigma.ext ((hs j).symm) (cast_heq _ _)

/-- **The identification**: joint assignments are exactly the
well-typed states of the assignment interface — the dependent
carrier, read as an erased function type guarded by wellformedness. -/
theorem range_asnState :
    Set.range (asnState (Val := Val)) = {s | AsnWf s} := by
  ext s
  constructor
  · rintro ⟨a, rfl⟩
    exact fun j => rfl
  · intro hs
    exact ⟨asnOfState s hs, asnState_asnOfState s hs⟩

end AssignmentWire

/-! ## The graphical-model square, at the record space -/

section PgmFibre

variable {n : ℕ} {Val : Fin (n + 1) → Type} [∀ i, Fintype (Val i)]

/-- The compiled network's presentation at the record space: the
pushed constraint diagram, as a citizen of the semantic universe's
fibre over the assignment interface — by type. -/
noncomputable def pgmSpecW (R : Pgm.PgmRows n Val) :
    DnfSpec (asnWire Val) :=
  diagramDnf ((Pgm.atoms R).map (cmap asnState))

/-- The rows-grain wiring at the record space: the pushed ideal point
models the pushed presentation exactly when the intrinsic law is the
rows' law — the transported judgment bridge composed with the
network's feeding lemma. -/
theorem su_pgm_wiring_asnWire {R : Pgm.PgmRows n Val} (hR : R.WF)
    (μ : SubPMF (Pgm.Asn Val)) :
    idealPoint (μ.map asnState) ∈ (pgmSpecW R).modelClass
      ↔ μ = Pgm.rowsLaw R hR :=
  (idealPoint_map_mem_diagramDnf_iff asnState_injective
      (Pgm.atoms R) μ).trans (Pgm.satAtoms_iff hR μ)

/-- **The graphical-model square, in the fibre over the assignment
interface**: the pushed ideal point of a law models the compiled
network's pushed presentation exactly when the law is the chain-rule
joint. -/
theorem su_pgm_adequacy_asnWire (B : Pgm.FinBN n Val)
    (μ : SubPMF (Pgm.Asn Val)) :
    idealPoint (μ.map asnState)
        ∈ (pgmSpecW (Pgm.compile B)).modelClass
      ↔ μ = B.jointLaw := by
  rw [su_pgm_wiring_asnWire (Pgm.compile_wf B) μ, Pgm.compile_rowsLaw]

/-- The positive face at the network's corner, at the record space. -/
theorem su_pgm_jointLaw_mem_asnWire (B : Pgm.FinBN n Val) :
    idealPoint (B.jointLaw.map asnState)
      ∈ (pgmSpecW (Pgm.compile B)).modelClass :=
  (su_pgm_adequacy_asnWire B B.jointLaw).mpr rfl

/-- Ex falso at the network's corner, at the record space. -/
theorem su_pgm_bottom_asnWire (B : Pgm.FinBN n Val) :
    (⊤ : Plain.Pen (states (asnWire Val)))
      ∉ (pgmSpecW (Pgm.compile B)).modelClass :=
  top_notMem_diagramDnf _

end PgmFibre

end Adequacy

end SuFunctor
