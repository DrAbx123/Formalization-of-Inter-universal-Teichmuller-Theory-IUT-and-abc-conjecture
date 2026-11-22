import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual

/-!
# A541 consumer: actual S3137 paper readings for Cor 3.12

Consumes the green actual readings:
* `qPilotLogVolumeReading P = -|log q|` (`S3137QThetaPilotLogVolumeReadingsActual`);
* `thetaPilotHullLogVolumeReal C3` = actual Haar log-volume of the Theta-pilot hull
  (`S3137ThetaHullVolumeScalingActual`), with `thetaPilotHull = actualC3LogShellTensorRegion`.

The paper Cor 3.12 readout statement is packaged as a Prop with its finiteness,
q-nonpositivity and signed inequality components; the C_Theta form is derived
from the signed inequality (no new axiom).

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperReadoutConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance paperReadoutMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance paperReadoutBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- Paper Cor 3.12 readout statement on one C3 input and q-pilot object: the
Theta-hull reading is finite, the q reading is nonpositive, and the signed
inequality holds. -/
def PaperCor312Readout (P : PaperQPilotObjectActual (l := l) (I := I)) : Prop :=
  (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ ∧
    qPilotLogVolumeReading P ≤ 0 ∧
    qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3

theorem paperReadout_thetaHull_finite :
    (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ :=
  thetaPilotHull_measure_lt_top (C3 := C3)

theorem paperReadout_q_nonpos
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qPilotLogVolumeReading P ≤ 0 :=
  qPilotLogVolumeReading_nonpos P

theorem paperReadout_q_eq_neg_abs_log
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qPilotLogVolumeReading P = -|Real.log (‖P.line.C3.q.q‖)| :=
  qPilotLogVolumeReading_eq_neg_abs_qParameter P

theorem paperReadout_of_inequality
    (P : PaperQPilotObjectActual (l := l) (I := I))
    (h : qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3) :
    PaperCor312Readout C3 P :=
  ⟨paperReadout_thetaHull_finite C3, paperReadout_q_nonpos P, h⟩

/-- C_Theta form of the paper readout: if the Theta reading is `C * |log q|`
and the q reading is `-|log q|` with `|log q| > 0`, the signed inequality gives
`C >= -1`. -/
theorem paperReadout_CTheta_ge_neg_one
    (P : PaperQPilotObjectActual (l := l) (I := I))
    {qMag C : Real} (hq : 0 < qMag)
    (hqeq : qPilotLogVolumeReading P = -qMag)
    (hthetaeq : thetaPilotHullLogVolumeReal C3 = C * qMag)
    (hineq : qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3) :
    -1 ≤ C := by
  rw [hqeq, hthetaeq] at hineq
  have hmul : (-1 : Real) * qMag ≤ C * qMag := by
    calc (-1 : Real) * qMag = -qMag := by ring
      _ ≤ C * qMag := hineq
  exact le_of_mul_le_mul_right hmul hq

end LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperReadoutConsumerActual
