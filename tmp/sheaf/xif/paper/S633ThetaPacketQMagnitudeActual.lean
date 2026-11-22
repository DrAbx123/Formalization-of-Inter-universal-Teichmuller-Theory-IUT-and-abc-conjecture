import tmp.sheaf.xif.paper.PaperThetaMagnitudeComparisonProof
import tmp.sheaf.xif.paper.ThetaLinkFromSource
import tmp.sheaf.xif.paper.QPilotObjectActual
import tmp.sheaf.xif.paper.S627ThetaSourceComparisonActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S633ThetaPacketQMagnitudeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.XiFInequalityProof1
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeComparisonProof
open LeanFormal.IUT.XiFPaper.S627ThetaSourceComparisonActual

universe ua uv upi umon ui uC3 uD3 uM uP uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP}
  (l := l) (V := V) (I := I))
variable (P : PaperSignedHull X label)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The paper q-pilot magnitude equals the actual object q-pilot magnitude
when the object's C3 is the chosen C3. -/
theorem paperQPilotLogMagnitude_eq_qPilotLogMagnitude
    (hC3 : O.line.C3 = C3) :
    paperQPilotLogMagnitude C3 = O.qPilotLogMagnitude := by
  unfold paperQPilotLogMagnitude paperQPilotLogVolume
  unfold PaperQPilotObjectActual.qPilotLogMagnitude PaperQPilotObjectActual.signedQPilotLogVolume
  rw [hC3]

/-- Conditional proof of the paper xi-f comparison from the repo theta-packet
comparison theorem, procession alignment, and theta/q identification. -/
theorem missingPaperXiFComparison_of_thetaPacket
    (hC3 : O.line.C3 = C3)
    (hAlign : P.procession.average = actualThetaPacketAverage (l := l) C3)
    (hQ : ThetaPacketQIdentification (l := l) C3) :
    MissingPaperXiFComparison O P := by
  unfold MissingPaperXiFComparison paperComparisonGap
  have hbound := paperThetaMagnitudeComparison_of_packet_alignment (l := l) C3 P hAlign hQ
  unfold PaperThetaMagnitudeComparison at hbound
  rw [paperQPilotLogMagnitude_eq_qPilotLogMagnitude O C3 hC3] at hbound
  exact hbound

/-- Exact reduced gap: chosen C3 for O, procession average alignment, and
theta-packet q identification. -/
structure PaperThetaComparisonGap where
  C3 : SourcePilotRegionData (l := l) (V := V) I
  C3_eq : O.line.C3 = C3
  average_alignment : P.procession.average = actualThetaPacketAverage (l := l) C3
  theta_q_identification : ThetaPacketQIdentification (l := l) C3

/-- The reduced gap is sufficient for the paper comparison. -/
theorem missingPaperXiFComparison_of_gap
    (G : PaperThetaComparisonGap (l := l) (V := V) (I := I) O P) :
    MissingPaperXiFComparison O P :=
  missingPaperXiFComparison_of_thetaPacket O P G.C3 G.C3_eq
    G.average_alignment G.theta_q_identification

end LeanFormal.IUT.XiFPaper.S633ThetaPacketQMagnitudeActual

end
