import SuFunctor.Adequacy.CheckerCarrier
import Reflection.Accept

/-! # Acceptance as a semantic-universe theorem

The reflection route ends in `acceptBytesSealed_sound`: whatever claim
the sealed-byte acceptance function returns is semantically valid, the
returned proof object itself being the witness.  The checker face
(`SuFunctor.Plain.CheckerFace`) and the checker carrier
(`SuFunctor.Adequacy.CheckerCarrier`) identify that verdict with the
possibilistic face of the penalty judgment and with membership in the
semantic universe's fibre over the sequent's own wire object.  This
module records the composition — the end-to-end statement of the
route, one theorem per altitude:

* at the sequent's valuation carrier, as the vanishing upper
  probability of the conclusion's complement over the credal compile
  of the premise-and-admissibility cylinder
  (`acceptBytesSealed_face_sound`), and as membership of the
  cylinder's wall in the model class of the sequent's presentation
  (`acceptBytesSealed_modelClass_sound`);
* at the wire object's record space, as the same face read along the
  valuation embedding (`acceptBytesSealed_face_valWire_sound`), and —
  the headline — as a judgment in the semantic universe's fibre over
  the hypernet's wire object (`acceptBytesSealed_su_sound`).

Every proof is one line: an `Iff.mp` of a landed identification
applied to the route's landed soundness theorem.  That is the design,
not a shortcut — the route discharged every obligation during
elaboration, and the identifications were proven where their
vocabulary lives.  Like the route's own soundness statements, the
acceptance hypothesis appears only through the value it produced: the
validity travels inside the accepted claim, so no stage of decoding,
reconstruction, or elaboration is trusted here either.
-/

namespace SuFunctor

namespace Adequacy

open SuFunctor.Plain
open PPLC PPLC.Geolog

/-- **Acceptance at the face**: a claim accepted from sealed
certificate bytes has a semantically valid sequent, read as the
checker face — over the credal compile of the premise-and-
admissibility cylinder, the upper probability of the conclusion's
complement vanishes.  Stated at the sequent's own valuation carrier,
in the plain vocabulary throughout. -/
theorem acceptBytesSealed_face_sound (bs : Bytes) (a : Accepted)
    (h : acceptBytesSealed bs = some a) :
    upperProb (admCyl a.H a.seq) (postEvt a.H a.seq)ᶜ = 0 :=
  (semanticallyValid_iff_face a.H a.seq).mp
    (acceptBytesSealed_sound bs a h)

/-- **Acceptance at the model class**: the accepted sequent's verdict
as a coupled-judgment membership — the cylinder's wall belongs to the
model class of the sequent's single-disjunct presentation, at the
sequent's own valuation carrier. -/
theorem acceptBytesSealed_modelClass_sound (bs : Bytes) (a : Accepted)
    (h : acceptBytesSealed bs = some a) :
    cylWall a.H a.seq ∈ (sequentDnf a.H a.seq).modelClass :=
  (semanticallyValid_iff_mem_modelClass a.H a.seq).mp
    (acceptBytesSealed_sound bs a h)

/-- **Acceptance at the record space**: the checker face of the
accepted sequent, read over the state space of the hypernet's wire
object along the valuation embedding. -/
theorem acceptBytesSealed_face_valWire_sound (bs : Bytes)
    (a : Accepted) (h : acceptBytesSealed bs = some a) :
    upperProb (valState '' admCyl a.H a.seq)
      ((valState '' postEvt a.H a.seq))ᶜ = 0 :=
  (semanticallyValid_iff_face_valWire a.H a.seq).mp
    (acceptBytesSealed_sound bs a h)

/-- **Acceptance in the semantic universe**: a claim accepted from
sealed certificate bytes is a judgment in the semantic universe — the
cylinder's wall system belongs to the model class of the sequent's
presentation, in the fibre over the hypernet's wire object.  The
end-to-end theorem of the byte route: certificate bytes in, a fibre
citizenship out. -/
theorem acceptBytesSealed_su_sound (bs : Bytes) (a : Accepted)
    (h : acceptBytesSealed bs = some a) :
    cylWallW a.H a.seq ∈ (sequentSpec a.H a.seq).modelClass :=
  (semanticallyValid_iff_fibre a.H a.seq).mp
    (acceptBytesSealed_sound bs a h)

end Adequacy

end SuFunctor
