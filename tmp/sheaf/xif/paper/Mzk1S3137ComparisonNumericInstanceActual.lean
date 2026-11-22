import tmp.sheaf.xif.paper.Mzk1S3137ComparisonArithmeticActual
import tmp.sheaf.xif.paper.Mzk1ProcessionArithmeticInstanceActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3137 comparison numeric instance from the proved procession average

Connects the proved Unit L instance (`l=13`, `p=11`, `m=5`,
`average_thirteen = 35/12 log 11`) to the S3137 arithmetic reduction.  The
proportionality of the actual Haar hull to the procession average remains the
explicit named input; only the arithmetic comparison is proved here. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1S3137ComparisonNumericInstanceActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3137ComparisonArithmeticActual
open LeanFormal.IUT.XiFPaper.Mzk1ProcessionArithmeticInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1ProcessionContributionNumericsActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual

theorem processionAverage_eleven :
    processionAverage 5 6 (11 : Real) = (35 / 12) * Real.log (11 : Real) := by
  unfold processionAverage
  norm_num
  ring

theorem qPilotArithmeticVolume_thirteen :
    qPilotArithmeticVolume 5 6 (11 : Real) =
      -(5 * Real.log (11 : Real) / 26) := by
  unfold qPilotArithmeticVolume
  norm_num
  ring

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- The S3137 named comparison follows from the arithmetic instance once the
two explicit named identifications (hull average, q normalization) are supplied. -/
theorem qThetaComparison_of_numericInstance
    (hTheta : thetaPilotHullLogVolumeReal C3 =
      processionAverage 5 6 (11 : Real))
    (hq : qPilotLogVolumeReading P =
      qPilotArithmeticVolume 5 6 (11 : Real)) :
    qThetaPilotLogVolumeComparison C3 P :=
  (qThetaComparison_iff_arithmetic C3 P 5 6 (11 : Real) hTheta hq).mpr
    numeric_l13_p11_m5

end LeanFormal.IUT.XiFPaper.Mzk1S3137ComparisonNumericInstanceActual

end
