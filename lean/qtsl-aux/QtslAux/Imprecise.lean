import QtslAux.Imprecise.Credal
import QtslAux.Imprecise.Compose
import QtslAux.Imprecise.MarginalExtension
import QtslAux.Imprecise.TowerWitness
import QtslAux.Imprecise.InclusionWitness
import QtslAux.Imprecise.RegretSeatWitness
import QtslAux.Imprecise.BellmanGapRule
import QtslAux.Imprecise.BellmanGapCrystal
import QtslAux.Imprecise.MarginalCompat
import QtslAux.Imprecise.PenaltyCredalIso
import QtslAux.Imprecise.NaturalExtension
import QtslAux.Imprecise.NaturalExtensionGeneral
import QtslAux.Imprecise.Containment
import QtslAux.Imprecise.FeasibilityGlue
import QtslAux.Imprecise.ContainmentGeneral
import QtslAux.Imprecise.PenaltyEnvelope
import QtslAux.Imprecise.PenaltyKernelCompose
import QtslAux.Imprecise.MixedContraction
import QtslAux.Imprecise.WingCollapse
import QtslAux.Imprecise.HurwiczCrescents

/-! # Imprecise probability: finite credal sets and their composition

Umbrella module collecting the finite-support imprecise-probability development:
rational-valued probability mass functions and lower/upper expectations over
finite credal sets (`QtslAux.Imprecise.Credal`), two-stage composition
and the Hurwicz criterion (`Compose`), three-stage iteration
(`MarginalExtension`), explicit witnesses that the Hurwicz criterion is not
tower-consistent (`TowerWitness`), the seat-regret divergence witness —
same demonic envelope, different seat-regret truth, so no reading of the
closed subject's credal body expresses regret against a comparison seat
(`RegretSeatWitness`), the finitary soundness of the SRegretLE Bellman-gap
rule — benchmark and achieved telescopes, the graded δ-greedy form, the
finite-horizon instance (`BellmanGapRule`) — with its two negative
witnesses: once-drawn weather breaks the benchmark side, and greediness
purchases the numerator's γ (`BellmanGapCrystal`), the penalty calculus for marginal
compatibility (`MarginalCompat`), pushforward and lax-composition coherence
laws for penalty functionals (`PenaltyCoherence`), the isomorphism
between the penalty and credal presentations (`PenaltyCredalIso`),
coherent lower previsions with the finite envelope theorem and the
natural extension's universal property and LP duality
(`NaturalExtension`), the general-carrier envelope coherence and
natural-extension package over arbitrary measurable state spaces with
countably additive models — including the convexity and narrow-closedness
of the compatible set (`NaturalExtensionGeneral`), the containment of the composition law in the
least-committal glue with its crisp locus and strict witness
(`Containment`), and the properness-iff-marginal-compatibility
equivalence with the exact conditional-product witness
(`FeasibilityGlue`, consuming the standard-Borel `CouplingGlue`) — and the
penalty-kernel tier: family-presented penalty envelopes with the tropical
face and the finite Legendre transform of the threshold profile
(`PenaltyEnvelope`), the composition law whose intertwining square is exact
at finite support, with the once-drawn diagonal strictly below the fresh
composite (`PenaltyKernelCompose`), the mixed sum-product/max-plus
contraction identity with the exchange gap (`MixedContraction`), the
collapse of the timed-transition wing taxonomy into penalty-kernel
presentations (`WingCollapse`), and the crescent decomposition of Hurwicz
superlevels with its finitary strictness (`HurwiczCrescents`).
-/

