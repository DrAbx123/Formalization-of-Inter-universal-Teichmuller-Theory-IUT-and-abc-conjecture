import tmp.sheaf.xif.paper.Mzk1XiFFormalStepActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Cor 3.12 from the actual S3137 q/Theta comparison

The faithful comparison object is `qThetaPilotLogVolumeComparison C3 P`, i.e.
`qPilotLogVolumeReading P <= thetaPilotHullLogVolumeReal C3`, where the left
side is the actual q-pilot `-|log q|` and the right side is the actual Haar
log-volume of the literal Theta-pilot hull (`thetaPilotHull = actualRegion`).
This file consumes that comparison as an explicit named hypothesis and applies
the XiF formal step; it does not claim the comparison is proved. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312S3137AssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1XiFFormalStepActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- The StepXI contract whose two sides are the actual S3137 readings. -/
def contractOfS3137Comparison
    (h : qThetaPilotLogVolumeComparison C3 P) : StepXIContract where
  qSigned := qPilotLogVolumeReading P
  thetaSigned := thetaPilotHullLogVolumeReal C3
  targetSigned := qPilotLogVolumeReading P
  q_negative := P.signedQPilotLogVolume_neg
  ipl := True
  she := True
  apt := True
  ipl_evidence := trivial
  she_evidence := trivial
  apt_evidence := trivial
  q_le_target := le_rfl
  target_le_theta := h

/-- XiF formal step applied to the actual comparison yields `Cor312Conclusion`. -/
theorem cor312_of_s3137Comparison
    (h : qThetaPilotLogVolumeComparison C3 P) :
    Cor312Conclusion (contractOfS3137Comparison C3 P h) :=
  xi_f_formal_step h

/-- The same conclusion in membership form of the XiF region `R_{<= -|log Theta|}`. -/
theorem cor312_of_s3137Membership
    (h : qPilotLogVolumeReading P ∈ regionLe (thetaPilotHullLogVolumeReal C3)) :
    qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3 :=
  xi_f_formal_step h

end LeanFormal.IUT.XiFPaper.Mzk1Cor312S3137AssemblyActual

end
