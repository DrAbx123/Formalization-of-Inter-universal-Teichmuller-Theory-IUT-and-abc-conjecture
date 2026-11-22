import tmp.sheaf.xif.paper.Mzk1S3137ComparisonArithmeticActual
import tmp.sheaf.xif.paper.Mzk1SignedCor312AssemblyActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Signed readings from the S3137 arithmetic reduction

This is the arithmetic attempt for the S3137 comparison: once the actual Haar
hull reading is identified with the procession average and the actual q reading
with the arithmetic q volume, the comparison follows from the proved real
arithmetic instance.  The two identifications are explicit named inputs, not
same-region renamings. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1SignedComparisonArithmeticBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1S3137ComparisonArithmeticActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312AssemblyActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- Arithmetic route: hull-average and q-normalization identifications plus the
proved arithmetic inequality produce the actual S3137 readings. -/
theorem signedReadings_of_arithmetic
    (hTheta : thetaPilotHullLogVolumeReal C3 = processionAverage 5 6 (11 : Real))
    (hq : qPilotLogVolumeReading P = qPilotArithmeticVolume 5 6 (11 : Real))
    (hqneg : qPilotLogVolumeReading P < 0) :
    SignedReadings C3 P where
  qSigned := qPilotLogVolumeReading P
  thetaSigned := thetaPilotHullLogVolumeReal C3
  qSigned_eq_paper := rfl
  thetaSigned_eq_paper := rfl
  qSigned_neg := hqneg
  paper_comparison := by
    have hcmp : qThetaPilotLogVolumeComparison C3 P := by
      -- the arithmetic comparison from the proved numeric instance
      exact (qThetaComparison_iff_arithmetic C3 P 5 6 (11 : Real) hTheta hq).mpr
        numeric_l13_p11_m5
    exact hcmp

theorem cor312Conclusion_of_arithmetic
    (hTheta : thetaPilotHullLogVolumeReal C3 = processionAverage 5 6 (11 : Real))
    (hq : qPilotLogVolumeReading P = qPilotArithmeticVolume 5 6 (11 : Real))
    (hqneg : qPilotLogVolumeReading P < 0) :
    Cor312Conclusion
      (signedContract C3 (signedReadings_of_arithmetic C3 P hTheta hq hqneg)) :=
  cor312Conclusion_of_signedReadings C3 _

end LeanFormal.IUT.XiFPaper.Mzk1SignedComparisonArithmeticBridgeActual

end
