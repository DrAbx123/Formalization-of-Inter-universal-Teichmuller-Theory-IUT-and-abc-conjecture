import tmp.sheaf.xif.paper.Mzk1SignedLogVolumeCor312Actual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual

/-!
# A543 consumer: actual C3 signed log-volume <-> paper readings

Bridges the abstract signed log-volume (`Mzk1SignedLogVolumeCor312Actual`) to
the green actual S3137 readings on one C3 input:
* `actualSignedLogVolume C3 S := log (haar S).toReal` (the signed log-volume);
* `actualSignedLogVolume C3 (thetaPilotHull C3) = thetaPilotHullLogVolumeReal C3`;
* `qPilotLogVolumeReading P = -|log q|` (S3137, actual q reading);
* conditional xi-f bridge: if the q reading equals the signed q-region volume and
  the q-region volume is positive, then the paper signed inequality holds from
  containment + log monotonicity.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312ActualReadingBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeCor312Actual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance bridgeMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance bridgeBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- Actual signed log-volume of a region on the C3 tensor block. -/
noncomputable def actualSignedLogVolume (S : Set (C3LogShellTensorBlock C3)) : Real :=
  Real.log ((actualC3LogShellTensorHaar C3) S).toReal

theorem actualSignedLogVolume_apply (S : Set (C3LogShellTensorBlock C3)) :
    actualSignedLogVolume C3 S =
      Real.log ((actualC3LogShellTensorHaar C3) S).toReal := rfl

/-- The actual signed log-volume of the Theta-pilot hull is the paper Theta reading. -/
theorem actualSignedLogVolume_thetaHull :
    actualSignedLogVolume C3 (thetaPilotHull C3) = thetaPilotHullLogVolumeReal C3 :=
  rfl

/-- The q-pilot reading is the actual `-|log q|`. -/
theorem qPilotLogVolumeReading_eq_neg_abs
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qPilotLogVolumeReading P = -|Real.log (‖P.line.C3.q.q‖)| :=
  qPilotLogVolumeReading_eq_neg_abs_qParameter P

/-- Conditional xi-f bridge: if the q reading is the signed q-region volume
(positive) and the hull contains the q region, then the paper signed inequality
holds by log monotonicity. -/
theorem paper_signed_inequality_of_containment
    (P : PaperQPilotObjectActual (l := l) (I := I)) {qRegion : Set (C3LogShellTensorBlock C3)}
    (hcontain : qRegion ⊆ thetaPilotHull C3)
    (hreading : qPilotLogVolumeReading P = actualSignedLogVolume C3 qRegion)
    (hpos : 0 < (actualC3LogShellTensorHaar C3) qRegion)
    (hfin : (actualC3LogShellTensorHaar C3) qRegion ≠ ⊤) :
    qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3 := by
  rw [hreading]
  rw [show thetaPilotHullLogVolumeReal C3 = actualSignedLogVolume C3 (thetaPilotHull C3)
    from (actualSignedLogVolume_thetaHull C3).symm]
  unfold actualSignedLogVolume
  exact Real.log_le_log (ENNReal.toReal_pos (ne_of_gt hpos) hfin)
    (ENNReal.toReal_mono (ne_of_lt (thetaPilotHull_measure_lt_top (C3 := C3)))
      (measure_mono hcontain))

end LeanFormal.IUT.XiFPaper.Mzk1Cor312ActualReadingBridgeActual
