import SuFunctor.Universe.VietorisStratum

/-! # The credal-body poset: the seven classes

Credal bodies — nonempty closed radial subsets of the subprobability
carrier — are the set-side face of the lsc universe (`isClosed_compile_iff`:
a radial compile is closed exactly when its penalty is lower
semicontinuous; no shape axiom beyond that).  This module defines the
named subclasses whose inclusion poset the `CredalPoset` development
mechanizes:

* `IsCredalBody` — the house class (nonempty, closed, radial);
* `IsConvexCredalBody` — the convex subclass (the outgoing (C2)/(P2)
  "credal denotation" class of the chapter's earlier revision);
* `IsRichardsonBody` — compiles of penalty functionals both *convex*
  and *lsc* (the working reading of the probabilistic-dependency-graph
  programme's codomain; see the definition's docstring for provenance);
* `IsUltra` — Kosoy–Appel homogeneous ultracontributions: nonempty,
  topologically closed, convex, **pointwise**-down-closed;
* `IsMVS` — the Mio–Vignudelli–Sarkis `C^↓` shape: pointwise-down
  closures of finitely generated polytopes (nonempty);
* `IsHL` — Halpern–Leung MWER bodies: ultracontributions containing a
  full-mass member;
* `IsCozman` — classical credal sets (closed convex sets of full-mass
  states), radially embedded;
* `IsPrevisionBody` — bodies cut out by families of one-sided constraints
  `∫ h dν ≤ 1`, `h ≥ 0` — the Goubault-Larrecq
  `𝒞P^{≤1}_super` shape; `Previsions.lean` proves this class *equals*
  `IsUltra` on the finite stratum.

Everything is stated for `S : Set (BelState V)`; convexity of such a set
means convexity of its coercion image in `V → ℝ` (`ConvexBody`).  The
development was preregistered (definitions, predicted poset, witness
matrix, and mutant loci fixed before any proof was attempted); the
assembled poset lives in `SuFunctor.Universe.CredalPoset`.
-/

namespace SuFunctor.Universe

open scoped ENNReal

variable {V : Type*} [Fintype V]

namespace CredalPoset

/-! ## Carrier-side vocabulary -/

/-- The coercion image of a set of distributions inside `V → ℝ`. -/
def carrierImage (S : Set (BelState V)) : Set (V → ℝ) :=
  (fun x : BelState V => (x : V → ℝ)) '' S

theorem mem_carrierImage {S : Set (BelState V)} {x : BelState V}
    (hx : x ∈ S) : (x : V → ℝ) ∈ carrierImage S :=
  ⟨x, hx, rfl⟩

/-- Convexity for a set of distributions: convexity of its image in the
ambient function space.  (The carrier itself is convex, so mixtures of
members are again distributions.) -/
def ConvexBody (S : Set (BelState V)) : Prop :=
  Convex ℝ (carrierImage S)

/-- Pointwise-down closure: every distribution coordinatewise below a
member is a member.  This is the `⊥`-closure of the
Mio–Vignudelli–Sarkis / Kosoy–Appel order (mass may leak anywhere), and
is strictly stronger than ray-down closure (`IsRadial`). -/
def PtwiseDown (S : Set (BelState V)) : Prop :=
  ∀ y ∈ S, ∀ x : BelState V, (x : V → ℝ) ≤ (y : V → ℝ) → x ∈ S

/-- Mixture of two probability states (the flat carrier is convex). -/
def ProbState.mix (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (μ ν : ProbState V) : ProbState V :=
  ⟨s • (μ : V → ℝ) + t • (ν : V → ℝ),
    convex_probCarrier μ.2 ν.2 hs ht hst⟩

@[simp] theorem ProbState.coe_mix (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t = 1) (μ ν : ProbState V) :
    ((ProbState.mix s t hs ht hst μ ν : ProbState V) : V → ℝ)
      = s • (μ : V → ℝ) + t • (ν : V → ℝ) := rfl

/-- Convexity of a penalty functional on the flat carrier, quantified
over strictly interior mixture weights (the endpoint cases are
degenerate identities).  `ℝ≥0∞` arithmetic: with `s, t > 0` no
`0 * ⊤` corner arises on the right-hand side. -/
def PenaltyConvex (f : ProbPenalty V) : Prop :=
  ∀ μ ν : ProbState V, ∀ s t : ℝ, ∀ hs : 0 < s, ∀ ht : 0 < t,
    ∀ hst : s + t = 1,
    f (ProbState.mix s t hs.le ht.le hst μ ν)
      ≤ ENNReal.ofReal s * f μ + ENNReal.ofReal t * f ν

/-! ## The seven classes -/

/-- The house class: a **credal body** is a nonempty, topologically
closed, ray-down-closed subset of the subprobability carrier.  These are
exactly the radial compiles of lower semicontinuous penalty functionals
(`isClosed_compile_iff` + `isRadial_compile`); no convexity is imposed —
citizenship is lower semicontinuity, and nothing else. -/
def IsCredalBody (S : Set (BelState V)) : Prop :=
  S.Nonempty ∧ IsClosed S ∧ IsRadial S

/-- The convex subclass: the outgoing "(C2)/(P2) credal denotation"
class of the chapter's earlier revision. -/
def IsConvexCredalBody (S : Set (BelState V)) : Prop :=
  IsCredalBody S ∧ ConvexBody S

/-- Richardson bodies: radial compiles of penalty functionals that are
both *convex* and *lower semicontinuous*.  Provenance, stated
carefully: the probabilistic-dependency-graph programme
(Richardson–Halpern) never axiomatizes a codomain class — convexity of
its inconsistency measure is proved there as a lemma, and
semicontinuity is never mentioned — so this class is the programme's
*working reading*, with both properties assumed of its penalty
functionals (its conditional-relative-entropy family satisfies both).
The lsc conjunct is not redundant given convexity:
`exists_penaltyConvex_compile_not_richardson` (in `Adjudication`)
exhibits a convex penalty whose compile is no Richardson body.  (No
properness axiom; see the prereg's frozen note 1 for the
`∃ μ, f μ ≠ ⊤` variant, which moves only the bottom body's
membership.) -/
def IsRichardsonBody (S : Set (BelState V)) : Prop :=
  ∃ f : ProbPenalty V,
    PenaltyConvex f ∧ LowerSemicontinuous f ∧ S = compile f

/-- Kosoy–Appel homogeneous ultracontributions: nonempty, topologically
closed, convex, pointwise-down-closed sets of subprobability states. -/
def IsUltra (S : Set (BelState V)) : Prop :=
  S.Nonempty ∧ IsClosed S ∧ ConvexBody S ∧ PtwiseDown S

/-- The pointwise-down closure of the polytope spanned by a finite set
of distributions. -/
def ptwiseDownHull (F : Finset (BelState V)) : Set (BelState V) :=
  {x | ∃ y ∈ convexHull ℝ (carrierImage (F : Set (BelState V))),
    (x : V → ℝ) ≤ y}

/-- The Mio–Vignudelli–Sarkis `C^↓` class: pointwise-down closures of
nonempty finitely generated polytopes of subprobability states. -/
def IsMVS (S : Set (BelState V)) : Prop :=
  ∃ F : Finset (BelState V), F.Nonempty ∧ S = ptwiseDownHull F

/-- Halpern–Leung MWER bodies: ultracontributions containing at least
one full-mass member (the canonical weighted set of probabilities has a
weight-`1` element). -/
def IsHL (S : Set (BelState V)) : Prop :=
  IsUltra S ∧ ∃ x ∈ S, BelState.mass x = 1

/-- The radial embedding `[0,1] • K` of a set of distributions. -/
def scaleSegment (K : Set (BelState V)) : Set (BelState V) :=
  {z | ∃ x ∈ K, ∃ t : ℝ, ∃ h0 : 0 ≤ t, ∃ h1 : t ≤ 1,
    z = BelState.scale t h0 h1 x}

/-- Classical credal sets (Cozman et al.): nonempty closed convex sets
of *probability* (full-mass) states, entering the poset through their
radial embedding. -/
def IsCozman (S : Set (BelState V)) : Prop :=
  ∃ K : Set (BelState V), K.Nonempty ∧ IsClosed K ∧ ConvexBody K
    ∧ (∀ x ∈ K, BelState.mass x = 1) ∧ S = scaleSegment K

/-- Prevision-shaped bodies: cut out by an arbitrary family of one-sided
constraints `∑ v, x v * h v ≤ 1` with nonnegative gambles `h` — the
finite-stratum face of Goubault-Larrecq's `𝒞P^{≤1}_super` hyperspace
(each constraint is a superlinear-prevision sublevel; on a finite
outcome space every gamble is lower semicontinuous). -/
def IsPrevisionBody (S : Set (BelState V)) : Prop :=
  ∃ H : Set (V → ℝ), (∀ h ∈ H, ∀ v, 0 ≤ h v)
    ∧ S = {x : BelState V | ∀ h ∈ H, ∑ v, (x : V → ℝ) v * h v ≤ 1}

/-! ## First bridges (the cheap inclusions) -/

/-- Scaling is pointwise decrease: ray-down closure follows from
pointwise-down closure. -/
theorem PtwiseDown.isRadial {S : Set (BelState V)} (h : PtwiseDown S) :
    IsRadial S := by
  intro x hx t h0 h1
  refine h x hx _ fun v => ?_
  rw [BelState.coe_scale]
  calc t * (x : V → ℝ) v ≤ 1 * (x : V → ℝ) v := by
        exact mul_le_mul_of_nonneg_right h1 (x.nonneg v)
    _ = (x : V → ℝ) v := one_mul _

/-- A nonempty radial set owns the zero state. -/
theorem zero_mem_of_isRadial {S : Set (BelState V)} (hS : S.Nonempty)
    (hrad : IsRadial S) : BelState.zero V ∈ S := by
  obtain ⟨x, hx⟩ := hS
  have h := hrad x hx 0 le_rfl zero_le_one
  have hzero : BelState.scale 0 le_rfl zero_le_one x = BelState.zero V := by
    apply Subtype.ext
    funext v
    rw [BelState.coe_scale]
    simp [BelState.zero]
  rwa [hzero] at h

/-- **T1**: convex credal bodies are credal bodies. -/
theorem IsConvexCredalBody.isCredalBody {S : Set (BelState V)}
    (h : IsConvexCredalBody S) : IsCredalBody S := h.1

/-- **T3**: ultracontributions are convex credal bodies. -/
theorem IsUltra.isConvexCredalBody {S : Set (BelState V)}
    (h : IsUltra S) : IsConvexCredalBody S :=
  ⟨⟨h.1, h.2.1, h.2.2.2.isRadial⟩, h.2.2.1⟩

/-- **T5**: Halpern–Leung bodies are ultracontributions. -/
theorem IsHL.isUltra {S : Set (BelState V)} (h : IsHL S) : IsUltra S :=
  h.1

end CredalPoset

end SuFunctor.Universe
