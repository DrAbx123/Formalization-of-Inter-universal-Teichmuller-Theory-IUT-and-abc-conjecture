import tmp.sheaf.xif.paper.ThetaLinkLogKummerActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume

/-!
# Corrected source signed log-volumes

The old sourceSetVolume is an ENNReal supremum of ENNReal.ofReal
sourceLocalLogDegree. Negative log-degrees are truncated to zero by
ENNReal.ofReal, so the signed hull comparison built from its toReal can lose
negative contributions.

This file replaces the hull side by the actual positive theta log-volume
sum_j -log (I.thetaValueAt n 0 j), and the q side by the actual q-pilot
signed log I.qPilotSignedLogVolume. The comparison is the exact signed
inequality, equivalently the positive inequality
correctedSourceHullLogVolume <= correctedSourceQPilotMagnitude.

No trivial nonnegativity direction is used and no inequality is asserted.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.SourceSignedLogVolumeCorrectedActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (n : ThetaPilotCarrier l)

/-- Actual positive Theta hull log-volume from theta values, with no
ENNReal.ofReal truncation. -/
noncomputable def correctedSourceHullLogVolume (v : V) : Real :=
  ∑ j : SignedLabel l.value,
    - Real.log (I.thetaValueAt (n.val : Int) 0 j)

/-- The corrected signed hull volume -|log(Theta)|. -/
noncomputable def correctedSourceSignedHullLogVolume (v : V) : Real :=
  - correctedSourceHullLogVolume (I := I) (v := v) (n := n)

/-- Actual q-pilot signed log-volume. -/
noncomputable def correctedSourceSignedImageLogVolume : Real :=
  I.qPilotSignedLogVolume

/-- The corrected q-pilot magnitude. -/
noncomputable def correctedSourceQPilotMagnitude : Real :=
  - correctedSourceSignedImageLogVolume (I := I)

/-- Corrected paper xi-f signed comparison. -/
def CorrectedSourceXifComparison (v : V) : Prop :=
  correctedSourceSignedImageLogVolume (I := I) <=
    correctedSourceSignedHullLogVolume (I := I) (v := v) (n := n)

/-- The corrected signed comparison is exactly the positive inequality
q-pilot magnitude >= Theta hull positive log-volume. -/
theorem correctedSourceXifComparison_iff_positive (v : V) :
    CorrectedSourceXifComparison (I := I) (v := v) (n := n) <->
      correctedSourceHullLogVolume (I := I) (v := v) (n := n) <=
        correctedSourceQPilotMagnitude (I := I) := by
  unfold CorrectedSourceXifComparison correctedSourceSignedImageLogVolume
    correctedSourceSignedHullLogVolume correctedSourceQPilotMagnitude
  change I.qPilotSignedLogVolume <= -correctedSourceHullLogVolume n v <->
    correctedSourceHullLogVolume n v <= -I.qPilotSignedLogVolume
  constructor <;> intro h <;> linarith

/-- The corrected signed hull volume is the negative of the positive theta sum. -/
theorem correctedSourceSignedHullLogVolume_eq (v : V) :
    correctedSourceSignedHullLogVolume (I := I) (v := v) (n := n) =
      -∑ j : SignedLabel l.value,
        -Real.log (I.thetaValueAt (n.val : Int) 0 j) := rfl

/-- No sourceSetVolume/ENNReal.ofReal occurs in the corrected hull value. -/
theorem correctedSourceHullLogVolume_eq_theta_sum (v : V) :
    correctedSourceHullLogVolume (I := I) (v := v) (n := n) =
      ∑ j : SignedLabel l.value,
        -Real.log (I.thetaValueAt (n.val : Int) 0 j) := rfl

end LeanFormal.IUT.XiFPaper.SourceSignedLogVolumeCorrectedActual

end