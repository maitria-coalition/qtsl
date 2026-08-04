import SuFunctor.Stochastic.NoiseKleisli
import SuFunctor.Adequacy.SemanticUniverseWiring

/-! # Adequacy: probabilistic programs (the former-level square)

The probabilistic-program former's formation data is deliberately the
chain former's, verbatim: the discrete-time slice of a probabilistic
program *is* an outcome-row kernel.  What distinguishes the entry is
its **reading** — the mechanism presents a program's *loop*: a start
stage and a loop body, each a noise-port hypernet stage (a
deterministic measurable map with randomness entering only at its
noise ports).  This module states the former-level square: the
compiled outcome-row presentation of a program, judged in the semantic
universe, pins exactly the noise-port denotation of the unrolled
program text.

Three strata, tied in order:

* **The text-equals-iterate law** (`noiseDenot_progTraj`, measure
  stratum, unconditional): the denotation of the *unrolled program
  text* — one deterministic map on one summed-roster cube, every draw
  at the interface, the evaluator never sampling — equals the
  kernel-local Kleisli iterate of the stage denotations (`pathDist`).
  This is the Kleisli functoriality law (`noiseDenot_seqComp`) folded
  from two stages to the former's grain: it licenses every consumer to
  reason kernel-locally about a program's loop, at every horizon.  It
  holds for *every* measurable program; no rationality is assumed.

* **The profile theorem** (`pathDist_profile`): two program texts with
  the same stage denotations — even at different noise arities — have
  the same path distribution at every horizon.  A model type is a
  profile, not a tag: the former's semantic content is exactly its
  kernel profile, and the program text beyond its kernels is
  presentation.

* **The square** (`su_pprog_adequacy`, exact stratum): for a program
  whose stage denotations have exact-rational faces (`Presents` — the
  program presents a classical chain), membership of a law's ideal
  point at the semantic universe's judgment on the compiled
  presentation (`pprogDnf`, the chain former's presentation under the
  probabilistic-program former's name) holds exactly when the law's
  real face *is* the unrolled text's denotation.  The judgment's
  citizens are exact-rational laws, and the boundary is stated rather
  than smoothed: a program enters the judgment through the rational
  face of its stage kernels, carried as a hypothesis; general
  programs — quantile-alias stages included — stop at the
  unconditional measure-stratum law above.

Two boundaries worth naming.  *Formation*: the reference measure is
the unit cube and total mass one is a theorem (`sum_noiseDenotFun`),
so an improper (unnormalizable) noise source is not a noise-port
object at all — excluded at formation, not at the square.  *Roster
discipline*: `progTraj`'s roster arithmetic allocates fresh ports to
every loop iteration by construction — sharing a draw across
iterations is unrepresentable in its type, and this is content, not
bookkeeping: with a shared roster the Kleisli law fails
(`copy_ne_kleisli`), so the discipline is exactly what the square's
left edge needs in order to exist. -/

namespace SuFunctor

universe u

/-! ## The real face of an exact-rational law -/

namespace SubPMF

variable {V : Type u}

/-- The real face of an exact-rational law: its weight function read
in `ℝ`.  The comparison seam between the judgment's citizens and the
noise-port denotations, which are real-valued by construction. -/
def probFun (μ : SubPMF V) : V → ℝ := fun v => (μ.wt v : ℝ)

@[simp] theorem probFun_apply (μ : SubPMF V) (v : V) :
    μ.probFun v = (μ.wt v : ℝ) := rfl

/-- No information is lost at the real face: the rational cast is
injective, so a law is pinned by its real face. -/
theorem probFun_injective : Function.Injective (probFun (V := V)) := by
  intro μ ν h
  apply SubPMF.ext'
  ext a
  have h1 := congrFun h a
  rw [probFun_apply, probFun_apply] at h1
  exact_mod_cast h1

end SubPMF

namespace Adequacy

open Stochastic Universe

variable {S : Type} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [MeasurableSingletonClass S]
variable {N₀ N : ℕ}

/-! ## Trajectory record spaces are noise-port codomains

(Singletons of the trajectory record space are measurable through the
library's pi instance: a trajectory is pinned by finitely many
coordinate observations.) -/

/-- The horizon-`0` trajectory at a state: one observed state, no
transitions. -/
def trajZero (s : S) : Traj S 0 := fun _ => s

omit [Fintype S] [DecidableEq S] [MeasurableSingletonClass S] in
theorem measurable_trajZero : Measurable (trajZero (S := S)) :=
  measurable_pi_lambda _ fun _ => measurable_id'

omit [Fintype S] [DecidableEq S] [MeasurableSingletonClass S] in
/-- Appending a state to a trajectory is measurable in the appended
state: every coordinate of the extension is a constant or the
identity. -/
theorem measurable_snoc {k : ℕ} (ω : Traj S k) :
    Measurable fun s : S => (Fin.snoc ω s : Traj S (k + 1)) := by
  refine measurable_pi_lambda _ fun i => ?_
  induction i using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using measurable_id'
  | cast j => simpa only [Fin.snoc_castSucc] using measurable_const

/-! ## The former's program grain: the mechanism presents a loop -/

/-- A probabilistic program at the former's grain: a start stage and a
loop body, each a noise-port hypernet stage — a deterministic
measurable map whose randomness enters only at its noise ports.  The
start stage reads `N₀` ports; each loop iteration reads `N` fresh
ports. -/
structure ProbProgram (S : Type) [MeasurableSpace S] (N₀ N : ℕ) where
  /-- The start stage: the initial state as a function of the start
  roster's draws. -/
  start : (Fin N₀ → ℝ) → S
  /-- The loop body: the next state as a function of the current state
  and one iteration's fresh draws. -/
  body : S → (Fin N → ℝ) → S
  measurable_start : Measurable start
  measurable_body : ∀ s, Measurable (body s)

namespace ProbProgram

/-- The start stage's kernel: the noise-port denotation of the start
text. -/
noncomputable def startDenot (P : ProbProgram S N₀ N) : ProbState S :=
  noiseDenot P.start P.measurable_start

/-- The loop body's kernel at a state: the noise-port denotation of
one iteration's text. -/
noncomputable def stepDenot (P : ProbProgram S N₀ N) (s : S) : ProbState S :=
  noiseDenot (P.body s) (P.measurable_body s)

end ProbProgram

/-- The summed roster of the unrolled text: the start roster plus one
fresh iteration roster per step.  Fresh ports for every iteration is
carried by the arithmetic itself — sharing a draw across iterations is
unrepresentable downstream. -/
def rosterLen (N₀ N : ℕ) : ℕ → ℕ
  | 0 => N₀
  | k + 1 => rosterLen N₀ N k + N

/-- The unrolled program text at horizon `k`: one deterministic map on
the summed-roster cube, emitting the whole visited trajectory.  Every
draw enters at the interface; the evaluator never samples. -/
def progTraj (P : ProbProgram S N₀ N) :
    (k : ℕ) → (Fin (rosterLen N₀ N k) → ℝ) → Traj S k
  | 0 => fun u => trajZero (P.start u)
  | k + 1 => seqComp (progTraj P k)
      fun ω u => (Fin.snoc ω (P.body (ω (Fin.last k)) u) : Traj S (k + 1))

theorem measurable_progTraj (P : ProbProgram S N₀ N) :
    ∀ k, Measurable (progTraj P k)
  | 0 => by
    show Measurable fun u => trajZero (P.start u)
    exact measurable_trajZero.comp P.measurable_start
  | k + 1 => by
    show Measurable (seqComp (progTraj P k)
      fun ω u => (Fin.snoc ω (P.body (ω (Fin.last k)) u) : Traj S (k + 1)))
    exact measurable_seqComp (measurable_progTraj P k)
      fun ω => (measurable_snoc ω).comp (P.measurable_body (ω (Fin.last k)))

/-- The kernel-local path distribution: the Kleisli iterate of the
stage kernels over the trajectory record space — start, then one
`bind` per iteration, each appending the fresh state to the record. -/
noncomputable def pathDist (P : ProbProgram S N₀ N) :
    (k : ℕ) → ProbState (Traj S k)
  | 0 => ProbState.push trajZero P.startDenot
  | k + 1 => (pathDist P k).bind fun ω =>
      ProbState.push (Fin.snoc ω) (P.stepDenot (ω (Fin.last k)))

/-! ## The text-equals-iterate law (measure stratum, unconditional) -/

/-- **The unrolled text denotes the kernel-local iterate**: the
noise-port denotation of the horizon-`k` program text equals the
`k`-fold Kleisli iterate of the stage kernels.  The Kleisli
functoriality law (`noiseDenot_seqComp`) folded to the former's grain:
one application per unrolled iteration, with the appended record
coordinate carried by the pushforward law (`noiseDenot_comp`).  No
rationality is assumed: every measurable program is covered. -/
theorem noiseDenot_progTraj (P : ProbProgram S N₀ N) :
    ∀ k, noiseDenot (progTraj P k) (measurable_progTraj P k) = pathDist P k
  | 0 => by
    calc noiseDenot (progTraj P 0) (measurable_progTraj P 0)
        = noiseDenot (trajZero ∘ P.start)
            (measurable_trajZero.comp P.measurable_start) :=
          noiseDenot_congr rfl _ _
      _ = ProbState.push trajZero (noiseDenot P.start P.measurable_start) :=
          noiseDenot_comp P.start trajZero P.measurable_start _
      _ = pathDist P 0 := rfl
  | k + 1 => by
    have hstage : ∀ ω : Traj S k, Measurable fun u : Fin N → ℝ =>
        (Fin.snoc ω (P.body (ω (Fin.last k)) u) : Traj S (k + 1)) :=
      fun ω => (measurable_snoc ω).comp (P.measurable_body (ω (Fin.last k)))
    have hω : ∀ ω : Traj S k,
        noiseDenot (fun u =>
            (Fin.snoc ω (P.body (ω (Fin.last k)) u) : Traj S (k + 1)))
          (hstage ω)
          = ProbState.push (Fin.snoc ω) (P.stepDenot (ω (Fin.last k))) := by
      intro ω
      calc noiseDenot (fun u =>
              (Fin.snoc ω (P.body (ω (Fin.last k)) u) : Traj S (k + 1)))
            (hstage ω)
          = noiseDenot (Fin.snoc ω ∘ P.body (ω (Fin.last k)))
              ((measurable_snoc ω).comp (P.measurable_body _)) :=
            noiseDenot_congr rfl _ _
        _ = ProbState.push (Fin.snoc ω)
              (noiseDenot (P.body (ω (Fin.last k)))
                (P.measurable_body _)) :=
            noiseDenot_comp _ _ (P.measurable_body _) _
        _ = ProbState.push (Fin.snoc ω) (P.stepDenot (ω (Fin.last k))) := rfl
    calc noiseDenot (progTraj P (k + 1)) (measurable_progTraj P (k + 1))
        = noiseDenot (seqComp (progTraj P k)
              fun ω u =>
                (Fin.snoc ω (P.body (ω (Fin.last k)) u) : Traj S (k + 1)))
            (measurable_seqComp (measurable_progTraj P k) hstage) :=
          noiseDenot_congr rfl _ _
      _ = (noiseDenot (progTraj P k) (measurable_progTraj P k)).bind
            fun ω => noiseDenot (fun u =>
                (Fin.snoc ω (P.body (ω (Fin.last k)) u) : Traj S (k + 1)))
              (hstage ω) :=
          noiseDenot_seqComp _ _ (measurable_progTraj P k) hstage
      _ = (pathDist P k).bind fun ω =>
            ProbState.push (Fin.snoc ω) (P.stepDenot (ω (Fin.last k))) := by
          rw [noiseDenot_progTraj P k]
          exact congrArg ((pathDist P k).bind) (funext hω)
      _ = pathDist P (k + 1) := rfl

/-! ## The profile theorem: a model type is a profile, not a tag -/

omit [DecidableEq S] in
/-- **The profile determines the path distribution**: two program
texts with the same stage denotations — even at different noise
arities — have the same path distribution at every horizon.  The
former's semantic content is exactly its kernel profile; the text
beyond its kernels is presentation. -/
theorem pathDist_profile {N₀' N' : ℕ} {P : ProbProgram S N₀ N}
    {Q : ProbProgram S N₀' N'}
    (hstart : P.startDenot = Q.startDenot)
    (hstep : ∀ s, P.stepDenot s = Q.stepDenot s) :
    ∀ k, pathDist P k = pathDist Q k
  | 0 => by
    show ProbState.push trajZero P.startDenot
      = ProbState.push trajZero Q.startDenot
    rw [hstart]
  | k + 1 => by
    show (pathDist P k).bind _ = (pathDist Q k).bind _
    rw [pathDist_profile hstart hstep k]
    refine congrArg ((pathDist Q k).bind) (funext fun ω => ?_)
    rw [hstep]

/-! ## The exact-rational face: a program presents a chain -/

/-- A program **presents** a classical chain when its stage
denotations are the chain's exact-rational entries, read in `ℝ`: the
start kernel is the initial distribution and the loop kernel is the
transition matrix.  This is the exact-stratum boundary of the square,
stated rather than smoothed: the judgment's citizens are
exact-rational laws, and a program enters the judgment through the
rational face of its stage kernels. -/
structure Presents (P : ProbProgram S N₀ N) (M : FinDTMC S) : Prop where
  start_eq : ∀ s, (P.startDenot : S → ℝ) s = (M.init s : ℝ)
  step_eq : ∀ s s', (P.stepDenot s : S → ℝ) s' = (M.step s s' : ℝ)

/-- **The presentation transfers to the record space**: if a program
presents a chain, its kernel-local path distribution is the real face
of the chain's classical path law, at every horizon.  The bind/push
composite collapses along the snoc decomposition of a trajectory,
matching the chain-weight product formula step for step. -/
theorem pathDist_presents {P : ProbProgram S N₀ N} {M : FinDTMC S}
    (h : Presents P M) :
    ∀ k (ω : Traj S k),
      ((pathDist P k : ProbState (Traj S k)) : Traj S k → ℝ) ω
        = ((M.pathLaw k).wt ω : ℝ)
  | 0 => by
    intro ω
    have hrhs : (M.pathLaw 0).wt ω = M.init (ω 0) := by
      rw [FinDTMC.pathLaw_wt]
      unfold chainWt
      rw [Fin.prod_univ_zero, mul_one]
    show pushFun trajZero (P.startDenot : S → ℝ) ω = ((M.pathLaw 0).wt ω : ℝ)
    rw [hrhs]
    have hcollapse : pushFun trajZero (P.startDenot : S → ℝ) ω
        = (P.startDenot : S → ℝ) (ω 0) := by
      refine (Finset.sum_eq_single (ω 0) ?_ ?_).trans ?_
      · intro s _ hs
        exact if_neg fun hc => hs (congrFun hc 0)
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
      · exact if_pos
          (funext fun i => congrArg ω (Subsingleton.elim (0 : Fin 1) i))
    rw [hcollapse]
    exact h.start_eq (ω 0)
  | k + 1 => by
    intro ω'
    have hsnoc :
        (Fin.snoc (Fin.init ω') (ω' (Fin.last (k + 1))) : Traj S (k + 1))
          = ω' :=
      Fin.snoc_init_self ω'
    show (∑ ω : Traj S k,
        ((pathDist P k : ProbState (Traj S k)) : Traj S k → ℝ) ω *
          pushFun (Fin.snoc ω) ((P.stepDenot (ω (Fin.last k))) : S → ℝ) ω')
      = ((M.pathLaw (k + 1)).wt ω' : ℝ)
    have houter : (∑ ω : Traj S k,
        ((pathDist P k : ProbState (Traj S k)) : Traj S k → ℝ) ω *
          pushFun (Fin.snoc ω) ((P.stepDenot (ω (Fin.last k))) : S → ℝ) ω')
        = ((pathDist P k : ProbState (Traj S k)) : Traj S k → ℝ)
            (Fin.init ω') *
          pushFun (Fin.snoc (Fin.init ω'))
            ((P.stepDenot ((Fin.init ω') (Fin.last k))) : S → ℝ) ω' := by
      refine Finset.sum_eq_single (Fin.init ω') ?_ ?_
      · intro ω _ hω
        have hz : pushFun (Fin.snoc ω)
            ((P.stepDenot (ω (Fin.last k))) : S → ℝ) ω' = 0 := by
          refine Finset.sum_eq_zero fun s _ => ?_
          refine if_neg fun hc => hω ?_
          have h2 := congrArg Fin.init hc
          rwa [Fin.init_snoc] at h2
        rw [hz, mul_zero]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    have hinner : pushFun (Fin.snoc (Fin.init ω'))
        ((P.stepDenot ((Fin.init ω') (Fin.last k))) : S → ℝ) ω'
        = ((P.stepDenot ((Fin.init ω') (Fin.last k))) : S → ℝ)
            (ω' (Fin.last (k + 1))) := by
      refine (Finset.sum_eq_single (ω' (Fin.last (k + 1))) ?_ ?_).trans ?_
      · intro s _ hs
        refine if_neg fun hc => hs ?_
        have h2 := congrFun hc (Fin.last (k + 1))
        rwa [Fin.snoc_last] at h2
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
      · exact if_pos hsnoc
    have hchain : chainWt M.init M.step ω'
        = chainWt M.init M.step (Fin.init ω') *
          M.step ((Fin.init ω') (Fin.last k)) (ω' (Fin.last (k + 1))) := by
      conv_lhs => rw [← hsnoc]
      rw [chainWt_snoc]
    rw [houter, hinner, pathDist_presents h k (Fin.init ω'), h.step_eq,
      FinDTMC.pathLaw_wt, FinDTMC.pathLaw_wt, hchain]
    push_cast
    ring

/-! ## The square, wired to the semantic universe -/

/-- The probabilistic-program former's compiled presentation: the
chain former's presentation, verbatim, under the former's own name —
the formation data is deliberately shared, and what distinguishes the
former is its reading (the mechanism presents a program's loop), which
lives on the classical side of the square. -/
noncomputable def pprogDnf (R : DtmcRows S) (k : ℕ) :
    SpecDnf (Plain.Joint (Traj S k)) :=
  dtmcDnf R k

omit [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [MeasurableSingletonClass S] in
@[simp] theorem pprogDnf_def (R : DtmcRows S) (k : ℕ) :
    pprogDnf R k = dtmcDnf R k := rfl

/-- The presented chain's path law has the program text's denotation
as its real face: the two edges of the square meet. -/
theorem pathLaw_probFun_eq {P : ProbProgram S N₀ N} {M : FinDTMC S}
    (hPM : Presents P M) (k : ℕ) :
    (M.pathLaw k).probFun
      = ((noiseDenot (progTraj P k) (measurable_progTraj P k) :
          ProbState (Traj S k)) : Traj S k → ℝ) := by
  rw [noiseDenot_progTraj P k]
  exact funext fun ω => (pathDist_presents hPM k ω).symm

/-- **The probabilistic-programs square, wired to the semantic
universe**: for a program presenting a chain, the ideal point of a law
models the compiled presentation exactly when the law's real face is
the noise-port denotation of the unrolled program text.  Left edge:
the program text through the Kleisli machinery
(`noiseDenot_progTraj`).  Right edge: the compiled outcome-row
presentation at the judgment (`su_dtmc_adequacy`, consumed whole).
The exact-rational boundary is the `Presents` hypothesis, not a
smoothing. -/
theorem su_pprog_adequacy {P : ProbProgram S N₀ N} {M : FinDTMC S}
    (hPM : Presents P M) (k : ℕ) (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈ (pprogDnf (compile M) k).modelClass
      ↔ μ.probFun = ((noiseDenot (progTraj P k) (measurable_progTraj P k) :
          ProbState (Traj S k)) : Traj S k → ℝ) := by
  show idealPoint μ ∈ (dtmcDnf (compile M) k).modelClass ↔ _
  rw [su_dtmc_adequacy M k μ]
  constructor
  · intro hμ
    rw [hμ]
    exact pathLaw_probFun_eq hPM k
  · intro he
    exact SubPMF.probFun_injective (he.trans (pathLaw_probFun_eq hPM k).symm)

/-- The positive face: the presented chain's path law models the
compiled presentation. -/
theorem su_pprog_pathLaw_mem {P : ProbProgram S N₀ N} {M : FinDTMC S}
    (hPM : Presents P M) (k : ℕ) :
    idealPoint (M.pathLaw k) ∈ (pprogDnf (compile M) k).modelClass :=
  (su_pprog_adequacy hPM k (M.pathLaw k)).mpr (pathLaw_probFun_eq hPM k)

omit [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- Ex falso at the former's corner: the inconsistent system models no
compiled program presentation. -/
theorem su_pprog_bottom (M : FinDTMC S) (k : ℕ) :
    (⊤ : Plain.Pen (Traj S k)) ∉ (pprogDnf (compile M) k).modelClass :=
  su_dtmc_bottom M k

/-! ## The specimen: a fair-coin program presents the fair chain

The presented subclass is inhabited, concretely: the program whose
start and loop body each read one fresh fair bit presents the
all-entries-one-half chain on `Bool`.  The square instantiates with
every hypothesis discharged — the judgment on the compiled fair chain
pins exactly the fair-coin text's denotation. -/

/-- The fair-coin program: one fresh fair bit per stage,
state-oblivious. -/
noncomputable def fairStep : ProbProgram Bool 1 1 where
  start := fun u => bit (u 0)
  body := fun _ u => bit (u 0)
  measurable_start := measurable_bitProj (0 : Fin 1)
  measurable_body := fun _ => measurable_bitProj (0 : Fin 1)

/-- The fair chain on `Bool`: every entry one half. -/
def fairChain : FinDTMC Bool where
  step := fun _ _ => 1 / 2
  init := fun _ => 1 / 2
  step_nonneg := fun _ _ => by norm_num
  step_row_sum := fun _ => by rw [Fintype.sum_bool]; norm_num
  init_nonneg := fun _ => by norm_num
  init_sum := by rw [Fintype.sum_bool]; norm_num

/-- The fair-coin program presents the fair chain: both stage kernels
are the fair Bernoulli state, whose weights are the chain's stored
halves. -/
theorem fairStep_presents : Presents fairStep fairChain where
  start_eq := fun s => by
    have hb : fairStep.startDenot = bern := noiseDenot_bitProj (0 : Fin 1)
    rw [hb]
    show (2⁻¹ : ℝ) = ((1 / 2 : ℚ) : ℝ)
    norm_num
  step_eq := fun s s' => by
    have hb : fairStep.stepDenot s = bern := noiseDenot_bitProj (0 : Fin 1)
    rw [hb]
    show (2⁻¹ : ℝ) = ((1 / 2 : ℚ) : ℝ)
    norm_num

/-- The square at the specimen: non-vacuously, with every hypothesis
discharged. -/
theorem su_fairStep_adequacy (k : ℕ) (μ : SubPMF (Traj Bool k)) :
    idealPoint μ ∈ (pprogDnf (compile fairChain) k).modelClass
      ↔ μ.probFun
        = ((noiseDenot (progTraj fairStep k)
            (measurable_progTraj fairStep k) :
          ProbState (Traj Bool k)) : Traj Bool k → ℝ) :=
  su_pprog_adequacy fairStep_presents k μ

end Adequacy

end SuFunctor
