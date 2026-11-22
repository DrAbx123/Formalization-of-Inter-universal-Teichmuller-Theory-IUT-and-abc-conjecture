import tmp.sheaf.xif.paper.S3139SourceMultiradialConsumerActual
import tmp.sheaf.xif.paper.MultiradialProcessionActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleOriginalInput
import tmp.sheaf.xif.paper.S3139FirstTriangleReadoutActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: multiradial-procession consumer (vendor-adapted from IUTIIIMultiradialProcession)

Adapted from the vendor promachina Stage1 structure
IUTIIIMultiradialProcession (Iut/Stage1/IUTStage1ConstructedTheorem311.lean:772,
with ofM2 at :797): a consumer-facing record bundling the actual multiradial
target input of the first triangle with the post-mutation q-pilot readout and
its comparison-region inclusion.  Vendor is not importable; the record is
re-proved with our objects.

**Component, not paper object.**  Registry frozen except approved re-pins.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139MultiradialProcessionConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.S3139SourceMultiradialConsumerActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleReadoutActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The consumer-facing multiradial procession of the first triangle: the actual
multiradial target input plus the q-pilot readout and its comparison-region
inclusion (the source-side q side of the q/Theta comparison). -/
structure SourceMultiradialProcessionConsumer
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- the actual multiradial target input (descended quotient representation) -/
  targetInput : SourceMultiradialTargetInput J
  /-- the post-mutation q-pilot signed log-volume -|log q| -/
  qSigned : ℝ
  /-- q is the actual q-pilot value: negative signed log-volume -/
  q_negative : qSigned < 0
  /-- the (fourth-triangle supplied) signed Theta-hull value -/
  hullValue : ℝ
  /-- the (xi-f)-shaped comparison-region inclusion -/
  inclusion : qSigned ≤ hullValue

/-- The canonical multiradial-procession consumer built from the actual source:
the target input and the q-pilot readout are constructed; only the
fourth-triangle hull value/inclusion are supplied. -/
noncomputable def sourceMultiradialProcessionConsumer
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (hq : (J.theaterAt 1 0).thetaPacket.q ≠ 1)
    (hullValue : ℝ) (hull_negative : hullValue < 0)
    (xif : sourceQPilotSignedLog J ≤ hullValue) :
    SourceMultiradialProcessionConsumer J where
  targetInput := sourceMultiradialTargetInput J
  qSigned := sourceQPilotSignedLog J
  q_negative := sourceQPilotSignedLog_neg J hq
  hullValue := hullValue
  inclusion := xif

/-- The q-side of the consumer is the actual post-mutation q-pilot log-volume. -/
theorem sourceMultiradialProcessionConsumer_qSigned
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (hq : (J.theaterAt 1 0).thetaPacket.q ≠ 1)
    (hullValue : ℝ) (hull_negative : hullValue < 0)
    (xif : sourceQPilotSignedLog J ≤ hullValue) :
    (sourceMultiradialProcessionConsumer J hq hullValue hull_negative xif).qSigned =
      sourceQPilotSignedLog J := rfl

end LeanFormal.IUT.XiFPaper.S3139MultiradialProcessionConsumerActual

end
