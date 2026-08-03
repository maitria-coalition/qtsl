import QtslAux.QuantumDeterminacy
import QtslAux.QuantumOuterStorey

/-! # Assembly: a kinematic fragment of locally covariant QFT

The locally covariant axioms of Brunetti–Fredenhagen–Verch
(arXiv:math-ph/0112041, Definition 2.1) package a quantum field theory
as a functor: isotone local algebras (i), Einstein causality (ii), and
the time-slice axiom (iii), with states handled set-valuedly (their
§5.1 proves a functorial choice of single states is unrealizable).
The preceding modules mechanized each clause at matrix grade over the
derived diamond site, one at a time.  This module assembles them into
one Lean object, `LCQFTFragment`, and proves the two-qubit system
under the σz ⊗ σz mechanism inhabits it.

**The fragment is a two-tier object, and honestly so.**  The σz ⊗ σz
coupling acts between the two fixed sites instantaneously: the
Heisenberg-evolved observables of one worldline need not commute with
those of the other at spacelike separation once the evolution times
differ (conjugating `1 ⊗ σx` by the flow produces a `σz ⊗ σy`
component, which fails to commute with `σx ⊗ 1`).  A non-relativistic
mechanism cannot carry microcausality — that would require local
dynamics, which lives on the far side of relative Cauchy evolution
(Fewster–Verch arXiv:1504.00586, §3.4) and is deliberately outside
this fragment.  The assembly therefore splits the axioms across two
tiers tied by a shadow equation:

* the **kinematic tier** — the net `net` carries isotony (i), Einstein
  causality (ii) in class-level form (every pointwise causally
  separated pair of diamonds has elementwise-commuting algebras), the
  site-exhaustion surrogate of (iii), derived-cover separation for
  states, and the record family;
* the **mechanism tier** — matter worldlines with exhaustive factors
  and a reversible mechanism, whose Heisenberg net satisfies genuine
  Cauchy-determinacy: the time-slice conclusion (iii) at both algebra
  and state grade.  Here determinacy is a *theorem* of complete
  initial data plus reversibility (`timeslice_genuine_alg`,
  `timeslice_genuine_state`), not a postulate;
* the **tie** — `frozen_shadow`: the kinematic net is exactly the
  frozen (constant-worldline, identity-mechanism) shadow of the
  matter data, so the two tiers describe one system, with and without
  its dynamics switched on.

**What "fragment" fences off**, stated here once and cited on the
fields: no same-physics claim across spacetimes (the SPASs property
fails for the full locally covariant class — Fewster–Verch
arXiv:1106.4785; its repair, dynamical locality, is defined through
relative Cauchy evolution); covariance across *different* spacetimes
enters only through order isomorphisms (the groupoid part; the site's
inclusions play the embedding role); the time-slice axiom's name is
qualified throughout (Haag–Schroer 1962, J. Math. Phys. 3, 248 — the
genuine tier is Cauchy-determinacy for finite matter content under a
reversible mechanism, and the surrogate tier is site-exhaustion).

A rank-0 disanalogy, owned rather than hidden: at this toy grade the
causality field's spacelike hypothesis is consumed only through site
disjointness (two causally separated diamonds cannot both contain a
site), and commutation is then tensor-factor disjointness.  In
continuum QFT the axiom constrains overlapping local algebras in a
way no finite two-site model can witness.  Relatedly, the landed
non-separating pair of diamonds touches the null cone at its corners
(the lower tip of one reaches the upper tip of the other along a null
segment), so it is *not* pointwise causally separated — the
class-level field exhibits its content instead at the degenerate
diamonds sitting exactly on the two sites, whose separation is the
landed spacelike fact about the sites themselves. -/

namespace Qtsl

namespace QuantumAssembly

open CategoryTheory Matrix DiamondSite QuantumDescent QuantumStates
open QuantumCovariance QuantumDeterminacy QuantumOuterStorey
open scoped ComplexOrder Kronecker

/-! ## The kinematic net, unfolded once

The two-site net's algebra assignment is a nested site-membership
conditional; the assembly's class-level causality proof needs it as a
rewriting equation rather than a `show`-pattern. -/

open scoped Classical in
/-- Definitional unfolding of the two-site net's algebra assignment. -/
theorem qubitNet_alg_def (D : Diamond (Mink ℝ)) :
    qubitNet.alg D =
      if inDiamond p D then
        (if inDiamond q D then ⊤ else leftFactor)
      else
        (if inDiamond q D then rightFactor else ⊥) := rfl

/-- Elements of the two tensor factors commute — microcausality's
mechanism at matrix grade: factor disjointness. -/
theorem commute_left_right {a b : TwoQubits} (ha : a ∈ leftFactor)
    (hb : b ∈ rightFactor) : Commute a b := by
  obtain ⟨x, rfl⟩ := mem_leftFactor.mp ha
  obtain ⟨y, rfl⟩ := mem_rightFactor.mp hb
  show _ * _ = _ * _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    one_mul, mul_one, one_mul, mul_one]

/-- **Einstein causality for the two-site net, class level**
(Brunetti–Fredenhagen–Verch Definition 2.1(ii) at fixed spacetime):
any two pointwise causally separated diamonds have elementwise
commuting algebras.  Causal separation forbids shared sites (a shared
site would be causally related to itself), so the algebras land in
disjoint tensor factors or in the scalars. -/
theorem qubitNet_einsteinCausal {D₁ D₂ : Diamond (Mink ℝ)}
    (hsp : ∀ ⦃r s : Mink ℝ⦄, inDiamond r D₁ → inDiamond s D₂ →
      ¬ r ≤ s ∧ ¬ s ≤ r) :
    ∀ a ∈ qubitNet.alg D₁, ∀ b ∈ qubitNet.alg D₂, Commute a b := by
  intro a ha b hb
  rw [qubitNet_alg_def] at ha hb
  by_cases hp₁ : inDiamond p D₁
  · have hp₂ : ¬ inDiamond p D₂ := fun h => (hsp hp₁ h).1 le_rfl
    rw [if_neg hp₂] at hb
    by_cases hq₁ : inDiamond q D₁
    · -- the first diamond holds both sites, so the second holds
      -- neither: its algebra is scalar.
      have hq₂ : ¬ inDiamond q D₂ := fun h => (hsp hq₁ h).1 le_rfl
      rw [if_neg hq₂, Algebra.mem_bot] at hb
      obtain ⟨c, rfl⟩ := hb
      show _ * _ = _ * _
      exact (Algebra.commutes c a).symm
    · rw [if_pos hp₁, if_neg hq₁] at ha
      by_cases hq₂ : inDiamond q D₂
      · rw [if_pos hq₂] at hb
        exact commute_left_right ha hb
      · rw [if_neg hq₂, Algebra.mem_bot] at hb
        obtain ⟨c, rfl⟩ := hb
        show _ * _ = _ * _
        exact (Algebra.commutes c a).symm
  · rw [if_neg hp₁] at ha
    by_cases hq₁ : inDiamond q D₁
    · have hq₂ : ¬ inDiamond q D₂ := fun h => (hsp hq₁ h).1 le_rfl
      rw [if_pos hq₁] at ha
      by_cases hp₂ : inDiamond p D₂
      · rw [if_pos hp₂, if_neg hq₂] at hb
        exact (commute_left_right hb ha).symm
      · rw [if_neg hp₂, if_neg hq₂, Algebra.mem_bot] at hb
        obtain ⟨c, rfl⟩ := hb
        show _ * _ = _ * _
        exact (Algebra.commutes c a).symm
    · rw [if_neg hq₁, Algebra.mem_bot] at ha
      obtain ⟨c, rfl⟩ := ha
      show _ * _ = _ * _
      exact Algebra.commutes c b

/-! ## The fragment -/

/-- **A kinematic fragment of a locally covariant QFT** at matrix
grade over the derived diamond site (Brunetti–Fredenhagen–Verch
arXiv:math-ph/0112041, Definition 2.1, fixed-spacetime shadow;
"fragment" is doing real work — see the module docstring for the
fences).  Two tiers, tied by a shadow equation:

* kinematic — `net` with class-level Einstein causality
  (Def. 2.1(ii)), the site-exhaustion surrogate of the time-slice
  axiom, an interiority-certified separation witness for derived-cover
  descent, and an exhaustive positive record family for the Born rows;
* mechanism — worldlines, exhaustive factors (complete initial data),
  and a reversible mechanism, from which genuine Cauchy-determinacy
  (Def. 2.1(iii)) at both algebra and state grade follows as a
  *theorem* (`timeslice_genuine_alg`/`timeslice_genuine_state`);
* the tie — `frozen_shadow`: the kinematic net is the
  constant-worldline, identity-mechanism shadow of the matter data.

States are handled set-valuedly throughout (`StatePresheaf net`),
per the no-preferred-state doctrine (BFV §5.1). -/
structure LCQFTFragment (X : Type*) [PartialOrder X]
    (n : Type*) [Fintype n] [DecidableEq n]
    (ι T κ : Type*) [Fintype κ] where
  /-- The kinematic observable net; its isotony is Def. 2.1(i)'s
  fixed-spacetime shadow. -/
  net : ObservableNet X n
  /-- The matter's initial sites. -/
  sites : ι → X
  /-- The matter worldlines. -/
  worldlines : ι → T → X
  /-- The observable factor carried by each matter worldline. -/
  factors : ι → Subalgebra ℂ (Matrix n n ℂ)
  /-- The reversible mechanism, Heisenberg picture. -/
  mechanism : T → (Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ)
  /-- Each site lies on its worldline. -/
  sites_on_worldlines : ∀ i, ∃ t, worldlines i t = sites i
  /-- Complete initial data: the factors jointly exhaust the matter
  algebra — the finite shadow of "a Cauchy surface carries complete
  initial data". -/
  factors_exhaustive : ⨆ i, factors i = ⊤
  /-- The tie between the tiers: the kinematic net is the frozen
  (constant-worldline, identity-mechanism) shadow of the matter
  data. -/
  frozen_shadow : ∀ D : Diamond X,
    (heisenbergNet (fun i (_ : T) => sites i) factors
      (fun _ => AlgEquiv.refl)).alg D = net.alg D
  /-- Einstein causality, class level (Def. 2.1(ii)): pointwise
  causally separated diamonds have elementwise commuting algebras. -/
  einstein_causality : ∀ {D₁ D₂ : Diamond X},
    (∀ ⦃r s : X⦄, inDiamond r D₁ → inDiamond s D₂ →
      ¬ r ≤ s ∧ ¬ s ≤ r) →
    ∀ a ∈ net.alg D₁, ∀ b ∈ net.alg D₂, Commute a b
  /-- The site-exhaustion surrogate of the time-slice axiom, per-site
  form: a subdiamond retaining every site its superdiamond holds
  carries the same algebra ("contains all the matter" plays "contains
  a Cauchy surface"; the honest disanalogy is at the genuine tier's
  theorems). -/
  timeslice_surrogate : ∀ {E D : Diamond X}, E ≤ D →
    (∀ i, inDiamond (sites i) D → inDiamond (sites i) E) →
    net.alg E = net.alg D
  /-- The chronology data of the derived site (interiority = the
  order-grade relative compactness the separation theorems consume,
  and the transport correspondent for covariance). -/
  kit : MixingKit X
  /-- The distinguished ambient diamond (the fixed spacetime's stand-in
  region, where separation and the record family are certified). -/
  ambient : Diamond X
  /-- The interiority witness for the ambient diamond. -/
  interior_witness : Diamond X
  /-- The witness is chronologically interior to the ambient
  diamond. -/
  interior_mem : kit.interiorMem ambient interior_witness
  /-- Attainment: the ambient algebra is already reached on the
  interior witness. -/
  interior_attained : net.alg ambient ≤ net.alg interior_witness
  /-- The record family: observables at the ambient diamond whose Born
  rows the state classes carry. -/
  records : κ → Matrix n n ℂ
  /-- The records are local to the ambient diamond. -/
  records_mem : ∀ α, records α ∈ net.alg ambient
  /-- The records are positive. -/
  records_posSemidef : ∀ α, (records α).PosSemidef
  /-- The records are exhaustive: a POVM row. -/
  records_exhaustive : ∑ α, records α = 1

namespace LCQFTFragment

variable {X : Type*} [PartialOrder X]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι T κ : Type*} [Fintype κ]
variable (F : LCQFTFragment X n ι T κ)

/-- The mechanism tier's net: the Heisenberg net of the matter data
with the dynamics switched on. -/
noncomputable abbrev mechanismNet : ObservableNet X n :=
  heisenbergNet F.worldlines F.factors F.mechanism

/-! ### The recovery checklist

Each clause of the kinematic package, as a theorem of the fragment.
Everything below is consumption of the preceding modules — the
assembly adds no proof mass, which is the point: the axioms hold. -/

/-- Def. 2.1(i), fixed-spacetime shadow: isotony. -/
theorem isotony {E D : Diamond X} (h : E ≤ D) :
    F.net.alg E ≤ F.net.alg D :=
  F.net.isotone h

/-- The surrogate tier at state grade: site-retaining restrictions are
bijective on state classes. -/
theorem timeslice_surrogate_state {E D : Diamond X} (hle : E ≤ D)
    (hs : ∀ i, inDiamond (F.sites i) D → inDiamond (F.sites i) E) :
    Function.Bijective (fun x =>
      (StatePresheaf F.net).map (homOfLE hle).op x) :=
  statePresheaf_restriction_bijective_of_alg_eq hle
    (F.timeslice_surrogate hle hs)

/-- **Def. 2.1(iii), genuine tier, algebra grade — a theorem, not a
postulate**: complete initial data plus a reversible mechanism give
Cauchy-determinacy on slice-covering subdiamonds. -/
theorem timeslice_genuine_alg {E D : Diamond X} (hle : E ≤ D) {t₀ : T}
    (hsl : CommonSlice F.worldlines t₀ E) :
    F.mechanismNet.alg E = F.mechanismNet.alg D :=
  heisenbergNet_alg_eq_of_commonSlice F.factors_exhaustive hle hsl

/-- Def. 2.1(iii), genuine tier, state grade: the state-presheaf
restriction along a slice-covering inclusion is a bijection on the
whole fibers (set-valued doctrine, BFV §5.1). -/
theorem timeslice_genuine_state {E D : Diamond X} (hle : E ≤ D)
    {t₀ : T} (hsl : CommonSlice F.worldlines t₀ E) :
    Function.Bijective (fun x =>
      (StatePresheaf F.mechanismNet).map (homOfLE hle).op x) :=
  heisenbergNet_commonSlice_restriction_bijective F.factors_exhaustive
    hle hsl

/-- Derived-cover separation at the ambient diamond: functionals
agreeing on every algebra of a derived cover agree globally. -/
theorem separation :
    ∀ S ∈ F.kit.diamondTopology F.ambient,
      SeparatesSieve F.net F.ambient S :=
  separates_of_interior_attained F.kit F.net F.interior_mem
    F.interior_attained

/-- The state presheaf is separated at every derived cover of the
ambient diamond (amalgamation uniqueness, in the site-theoretic
dress). -/
theorem statePresheaf_isSeparatedFor {S : Sieve F.ambient}
    (hS : S ∈ F.kit.diamondTopology F.ambient) :
    Presieve.IsSeparatedFor (StatePresheaf F.net) S.arrows :=
  isSeparatedFor_statePresheaf_of_interior_attained F.kit
    F.interior_mem F.interior_attained hS

/-- The record shadow: state classes at the ambient diamond to their
Born rows along the fragment's record family. -/
noncomputable def shadow :
    (StatePresheaf F.net).obj (Opposite.op F.ambient) → κ → ℝ :=
  recordShadowQ F.records F.records_mem

/-! ### Covariance: the fragment's certificates transport

The groupoid part of local covariance — order isomorphisms of event
carriers move every certified clause; inclusions already live inside
the site.  Pure consumption of the transport module. -/

/-- Separation transports: the pushforward net separates every derived
cover of the image diamond. -/
theorem separation_map {Y : Type*} [PartialOrder Y] (f : X ≃o Y)
    {M' : MixingKit Y}
    (hchron : ∀ a b : X, F.kit.chron a b ↔ M'.chron (f a) (f b)) :
    ∀ S' ∈ M'.diamondTopology (F.ambient.map f),
      SeparatesSieve (F.net.map f) (F.ambient.map f) S' :=
  map_separates_derived_of_interior_attained f hchron F.net
    F.interior_mem F.interior_attained

/-- Genuine Cauchy-determinacy transports, algebra grade. -/
theorem timeslice_genuine_alg_map {Y : Type*} [PartialOrder Y]
    (f : X ≃o Y) {E D : Diamond X} (hle : E ≤ D) {t₀ : T}
    (hsl : CommonSlice F.worldlines t₀ E) :
    (F.mechanismNet.map f).alg (E.map f) =
      (F.mechanismNet.map f).alg (D.map f) :=
  alg_eq_transport f (F.timeslice_genuine_alg hle hsl)

/-- Genuine Cauchy-determinacy transports, state grade. -/
theorem timeslice_genuine_state_map {Y : Type*} [PartialOrder Y]
    (f : X ≃o Y) {E D : Diamond X} (hle : E ≤ D) {t₀ : T}
    (hsl : CommonSlice F.worldlines t₀ E) :
    Function.Bijective (fun x =>
      (StatePresheaf (F.mechanismNet.map f)).map
        (homOfLE ((Diamond.map_le_map_iff f).mpr hle)).op x) :=
  restriction_bijective_transport f hle
    (F.timeslice_genuine_alg hle hsl)

end LCQFTFragment

/-! ## The instance: the two-qubit system under the σz ⊗ σz mechanism

Every field is discharged by a theorem of the preceding modules; the
one new proof in this module is the class-level causality lemma
above. -/

/-- The degenerate diamond at the left site. -/
def Dp : Diamond (Mink ℝ) := ⟨p, p, le_rfl⟩

/-- The degenerate diamond at the right site. -/
def Dq : Diamond (Mink ℝ) := ⟨q, q, le_rfl⟩

/-- The two site diamonds are pointwise causally separated — the
class-level causality hypothesis, nonvacuously instantiated (the
landed two-diamond pair around the sites touches the null cone at its
corners and is *not* pointwise separated; the degenerate diamonds sit
exactly on the spacelike sites). -/
theorem Dp_Dq_pointwise_spacelike :
    ∀ ⦃r s : Mink ℝ⦄, inDiamond r Dp → inDiamond s Dq →
      ¬ r ≤ s ∧ ¬ s ≤ r := by
  intro r s hr hs
  have hrp : r = p := le_antisymm hr.2 hr.1
  have hsq : s = q := le_antisymm hs.2 hs.1
  rw [hrp, hsq]
  exact p_q_spacelike

/-- **The two-qubit system under the σz ⊗ σz mechanism is a kinematic
fragment of a locally covariant QFT.**  The kinematic net, the two
static worldlines with their qubit factors, and the entangling flow
assemble into `LCQFTFragment`, each field discharged by a landed
theorem. -/
noncomputable def isingQubitFragment :
    LCQFTFragment (Mink ℝ) (Fin 2 × Fin 2) (Fin 2) ℝ (Fin 2 × Fin 2) where
  net := qubitNet
  sites := ![p, q]
  worldlines := qubitWorldline
  factors := qubitFactors
  mechanism := isingFlow
  sites_on_worldlines := by
    intro i
    fin_cases i
    · exact ⟨0, qubitWorldline_zero_zero⟩
    · exact ⟨0, qubitWorldline_one_zero⟩
  factors_exhaustive := qubitFactors_exhaustive
  frozen_shadow := heisenbergNet_const_id_alg_eq_qubitNet
  einstein_causality := qubitNet_einsteinCausal
  timeslice_surrogate := fun hle hs =>
    qubitNet_timeslice_surrogate hle (hs 0) (hs 1)
  kit := (minkowskiKit (E := ℝ)).toMixingKit
  ambient := Dstar
  interior_witness := E₃
  interior_mem := E₃_interior
  interior_attained := by rw [qubitNet_E₃]; exact le_top
  records := zzRecord
  records_mem := zzRecord_mem_top
  records_posSemidef := zzRecord_posSemidef
  records_exhaustive := zzRecord_sum

/-! ### The fragment's exhibits, read back through the assembly -/

/-- The fragment's mechanism net is the σz ⊗ σz Heisenberg net. -/
theorem isingQubitFragment_mechanismNet_eq :
    isingQubitFragment.mechanismNet = isingQubitNet := rfl

/-- Cauchy-determinacy at the concrete slice inclusion, algebra grade,
through the fragment. -/
theorem isingQubitFragment_slice_determinacy :
    isingQubitFragment.mechanismNet.alg Eslice =
      isingQubitFragment.mechanismNet.alg Dstar :=
  isingQubitFragment.timeslice_genuine_alg Eslice_le_Dstar
    qubitWorldline_commonSlice_Eslice

/-- Cauchy-determinacy at the concrete slice inclusion, state grade,
through the fragment. -/
theorem isingQubitFragment_slice_restriction_bijective :
    Function.Bijective (fun x =>
      (StatePresheaf isingQubitFragment.mechanismNet).map
        (homOfLE Eslice_le_Dstar).op x) :=
  isingQubitFragment.timeslice_genuine_state Eslice_le_Dstar
    qubitWorldline_commonSlice_Eslice

/-- Determinacy at every Minkowski translate, through the fragment's
transport clause. -/
theorem isingQubitFragment_translate_slice_determinacy (a v : ℝ) :
    (isingQubitFragment.mechanismNet.map (minkTranslate a v)).alg
        (Eslice.map (minkTranslate a v)) =
      (isingQubitFragment.mechanismNet.map (minkTranslate a v)).alg
        (Dstar.map (minkTranslate a v)) :=
  isingQubitFragment.timeslice_genuine_alg_map (minkTranslate a v)
    Eslice_le_Dstar qubitWorldline_commonSlice_Eslice

/-- Einstein causality, nonvacuously: the fragment's causality clause
at the two site diamonds. -/
theorem isingQubitFragment_causality_point_pair :
    ∀ a ∈ qubitNet.alg Dp, ∀ b ∈ qubitNet.alg Dq, Commute a b :=
  isingQubitFragment.einstein_causality Dp_Dq_pointwise_spacelike

/-- The fragment's record shadow separates the Bell and maximally
mixed classes — the record family carries information the causal
covers structurally miss, now read through the assembled object. -/
theorem isingQubitFragment_shadow_separates_bell_mixed :
    isingQubitFragment.shadow
        (stateClassMk qubitNet Dstar ⟨bell, bell_isState⟩) ≠
      isingQubitFragment.shadow
        (stateClassMk qubitNet Dstar ⟨mixed, mixed_isState⟩) :=
  recordShadowQ_separates_bell_mixed

end QuantumAssembly

end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumAssembly.qubitNet_alg_def
#print axioms Qtsl.QuantumAssembly.commute_left_right
#print axioms Qtsl.QuantumAssembly.qubitNet_einsteinCausal
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.isotony
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.timeslice_surrogate_state
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.timeslice_genuine_alg
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.timeslice_genuine_state
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.separation
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.statePresheaf_isSeparatedFor
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.separation_map
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.timeslice_genuine_alg_map
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.timeslice_genuine_state_map
#print axioms Qtsl.QuantumAssembly.Dp_Dq_pointwise_spacelike
#print axioms Qtsl.QuantumAssembly.isingQubitFragment
#print axioms Qtsl.QuantumAssembly.isingQubitFragment_mechanismNet_eq
#print axioms Qtsl.QuantumAssembly.isingQubitFragment_slice_determinacy
#print axioms Qtsl.QuantumAssembly.isingQubitFragment_slice_restriction_bijective
#print axioms Qtsl.QuantumAssembly.isingQubitFragment_translate_slice_determinacy
#print axioms Qtsl.QuantumAssembly.isingQubitFragment_causality_point_pair
#print axioms Qtsl.QuantumAssembly.isingQubitFragment_shadow_separates_bell_mixed
