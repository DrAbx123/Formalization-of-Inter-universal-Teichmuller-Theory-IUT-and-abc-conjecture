import tmp.sheaf.xif.paper.S3139FirstTriangleReadoutActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleData
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: which triangle the first-triangle data supplies (role map + fourth-triangle seam)

Per the team methodology note: the qualitative (IPL/SHE/APT) package does not
logically imply the numerical q/Theta bridge; the bridge must come from the
four-triangle structure, with the fourth triangle `(hull+det) circ (dsc)SHE + IPL`
producing the q/Theta comparison (IUT III, Corollary 3.12; Formalization of IUT
(2026-04) §4 :536-621).  This file makes the role split explicit and exposes the
seam by which the first-triangle output plugs into the fourth-triangle numerical
comparison owned by the shehdd stream.

Role split for the data constructed in this stream:

* first triangle (BPS -> multiradial representation): the mutation
  (`S3139FirstTriangleMutationActual`) with its (Ind1)/(Ind2)/(Ind3) invariance
  and the post-mutation readouts, in particular the actual q-pilot log-volume
  `-|log q|` from the `(1,0)` Theta packet
  (`S3139FirstTriangleReadoutActual`);
* qualitative evidence slots (IPL/APT/SHE): supplied as explicit propositions
  with their evidence, not derived from the numerical data;
* fourth triangle (numerical): the signed Theta-hull log-volume `-|log Theta|`,
  its finiteness/normalization, and the (xi-f)-shaped inclusion
  `-|log q| <= -|log Theta|` — these are produced by the fourth-triangle
  `(hull+det) circ (dsc)SHE + IPL` data (HDD/SHE sources, shehdd stream) and are
  NOT supplied by the first-triangle data.

**Component, not paper object.**  Named future consumer: the shehdd fourth
triangle / S3134 fourth-joint numerical comparison via
`firstTriangleQThetaSeam`.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139FirstTriangleTriangleRolesActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3139SourceMultiradialConsumerActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleReadoutActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. The role map -/

/-- Which of the four Stage-1 triangles a piece of data supplies. -/
inductive StageOneTriangleRole
  /-- the first triangle: BPS -> multiradial representation (actual mutation) -/
  | firstTriangle
  /-- the qualitative IPL/APT/SHE evidence slots -/
  | qualitativeEvidence
  /-- the fourth-triangle numerical q/Theta comparison (not supplied here) -/
  | fourthTriangleNumericalComparison
  deriving DecidableEq, Repr

/-- The roles supplied by the first-triangle data of this stream: the actual
mutation plus the explicit qualitative evidence slots.  The fourth-triangle
numerical comparison is *not* in the list. -/
def firstTriangleContributionRoles : List StageOneTriangleRole :=
  [.firstTriangle, .qualitativeEvidence]

/-- The fourth-triangle numerical comparison is a distinct role, produced by
the shehdd fourth triangle, not by the first-triangle data. -/
def fourthTriangleRole : StageOneTriangleRole :=
  .fourthTriangleNumericalComparison

/-! ## 2. The seam into the fourth-triangle numerical comparison -/

/-- The seam of the first triangle into the fourth-triangle numerical
comparison: the post-mutation q-pilot log-volume `-|log q|` supplies the
`qSigned` slot; the signed Theta-hull value and the (xi-f) inclusion are
supplied by the shehdd fourth-triangle data (`(hull+det) circ (dsc)SHE + IPL`).
The result is the named `SourceQThetaComparisonInput` whose conclusion is the
Corollary 3.12 ordered comparison. -/
noncomputable def firstTriangleQThetaSeam
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (hq : (J.theaterAt 1 0).thetaPacket.q ≠ 1)
    (hullValue : ℝ) (hull_negative : hullValue < 0)
    (xif : sourceQPilotSignedLog J ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) : SourceQThetaComparisonInput J :=
  sourceQThetaComparisonInputFromTheta J n m route hq hullValue
    hull_negative xif ipl she apt ipl_evidence she_evidence apt_evidence

/-- The q-side slot of the seam is the actual post-mutation q-pilot log-volume
`-|log q|`; this is the part supplied by the first triangle. -/
theorem firstTriangleQThetaSeam_qSigned
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (hq : (J.theaterAt 1 0).thetaPacket.q ≠ 1)
    (hullValue : ℝ) (hull_negative : hullValue < 0)
    (xif : sourceQPilotSignedLog J ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    (firstTriangleQThetaSeam J n m route hq hullValue hull_negative xif
      ipl she apt ipl_evidence she_evidence apt_evidence).qSigned =
        sourceQPilotSignedLog J := rfl

/-- The Θ-side slot and the (xi-f) inclusion are *passed through unchanged*:
they are the fourth-triangle data supplied by the shehdd stream, not computed
by the first triangle. -/
theorem firstTriangleQThetaSeam_hullValue
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (hq : (J.theaterAt 1 0).thetaPacket.q ≠ 1)
    (hullValue : ℝ) (hull_negative : hullValue < 0)
    (xif : sourceQPilotSignedLog J ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    (firstTriangleQThetaSeam J n m route hq hullValue hull_negative xif
      ipl she apt ipl_evidence she_evidence apt_evidence).hullValue =
        hullValue := rfl

/-- The seam feeds the Corollary 3.12 ordered conclusion through the S3138
source V2 pinned boundary: this is the consumption point of the shehdd
fourth-triangle numerical comparison. -/
theorem firstTriangleQThetaSeam_conclusion
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (hq : (J.theaterAt 1 0).thetaPacket.q ≠ 1)
    (hullValue : ℝ) (hull_negative : hullValue < 0)
    (xif : sourceQPilotSignedLog J ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    Cor312Conclusion
      ((firstTriangleQThetaSeam J n m route hq hullValue hull_negative xif
        ipl she apt ipl_evidence she_evidence apt_evidence).boundary.assembly.arithmetic.toContract) :=
  (firstTriangleQThetaSeam J n m route hq hullValue hull_negative xif
    ipl she apt ipl_evidence she_evidence apt_evidence).conclusion

end LeanFormal.IUT.XiFPaper.S3139FirstTriangleTriangleRolesActual

end
