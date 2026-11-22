import tmp.sheaf.xif.paper.ConcreteSourceComparisonActual
import tmp.sheaf.xif.paper.ConcreteSourceComparisonNumericActualAdapted

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S624FinalConcreteSourceComparisonGapActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.ConcreteSourceComparisonActual
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.XiFPaper.ConcreteSourceComparisonActual
open LeanFormal.IUT.XiFPaper.ConcreteSourceComparisonNumericActualAdapted
open LeanFormal.IUT.XiFPaper.PaperSignedHullSignedActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open MeasureTheory

universe ua uv upi umon ui uX uLabel uG uL uC

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (D : SourcePilotRegionDonors (l := l) (V := V) I)

/-- Exact final target reduction: the concrete source-comparison obstacle is
exactly the Gaussian signed-average / bad-q absolute-log inequality. -/
theorem concreteSourceComparisonObstacle_iff_gaussSum_le_badQAbsLog
    (O : PaperQPilotObject (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l) I
      (SelfGroup (sourceQPilotStrip (concreteBoundary (l := l)))) (sourceQPilotStrip (concreteBoundary (l := l))))
    (P : PaperSignedHull (PaperC6Carrier (l := l) (V := V)) (SignedLabel l.value))
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial)
    (hP : P.procession.average =
      (c3ThetaSignedProcession
        (actualSignedC3 (l := l) (V := V) (I := I) D)).average) :
    ConcreteSourceComparisonObstacle (l := l) I P ↔
      Real.log (5 : Real) *
          ((gaussExponentSum (l := l) : Real) /
            (Fintype.card (SignedLabel l.value) : Real)) ≤
        sourceBadQAbsLog I.initial :=
  concreteComparison_iff_gaussSum_le_badQAbsLog O D P hO hP

/-- The exact minimal gap in the concrete q-pilot / signed-hull data: the
Gaussian signed average is bounded by the source bad-q absolute log. -/
def FinalConcreteSourceComparisonGap : Prop :=
  Real.log (5 : Real) *
      ((gaussExponentSum (l := l) : Real) /
        (Fintype.card (SignedLabel l.value) : Real)) ≤
    sourceBadQAbsLog I.initial

theorem finalGap_iff_generic
    (O : PaperQPilotObject (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l) I
      (SelfGroup (sourceQPilotStrip (concreteBoundary (l := l)))) (sourceQPilotStrip (concreteBoundary (l := l))))
    (P : PaperSignedHull (PaperC6Carrier (l := l) (V := V)) (SignedLabel l.value))
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial)
    (hP : P.procession.average =
      (c3ThetaSignedProcession
        (actualSignedC3 (l := l) (V := V) (I := I) D)).average) :
    ConcreteSourceComparisonObstacle (l := l) I P ↔
      FinalConcreteSourceComparisonGap (l := l) I D :=
  concreteSourceComparisonObstacle_iff_gaussSum_le_badQAbsLog I D O P hO hP

end LeanFormal.IUT.XiFPaper.S624FinalConcreteSourceComparisonGapActualAdapted

end
