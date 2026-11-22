import tmp.sheaf.xif.paper.QPilotGlobalLogVolumeFromQActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Classical q-pilot log from the actual qVFamily order -/

namespace LeanFormal.IUT.XiFPaper.QPilotClassicalLogActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- Classical q-pilot log: finite sum of the local q orders times the log
of the actual residue norm base. -/
noncomputable def qPilotClassicalLog
    [Fintype (Bad (nativePlaceSelection X.S))] : Real :=
  ∑ b : Bad (nativePlaceSelection X.S),
    ((qVFamily X.S b).order : Real) *
      Real.log (residueNormBase ((nativeBadLift X.S).lift b))

/-- The classical log is the sum of the actual local log magnitudes. -/
theorem qPilotClassicalLog_eq_sum_localLogMagnitude
    [Fintype (Bad (nativePlaceSelection X.S))] :
    qPilotClassicalLog X =
      ∑ b : Bad (nativePlaceSelection X.S),
        localLogMagnitude (qVFamily X.S b) := by
  unfold qPilotClassicalLog
  apply Finset.sum_congr rfl
  intro b _
  rw [localLogMagnitude_eq_order_mul_log]

/-- The classical log is the negative sum of the actual local signed logs. -/
theorem qPilotClassicalLog_eq_neg_sum_localSignedLog
    [Fintype (Bad (nativePlaceSelection X.S))] :
    qPilotClassicalLog X =
      -∑ b : Bad (nativePlaceSelection X.S),
        localSignedLog (qVFamily X.S b) := by
  rw [qPilotClassicalLog_eq_sum_localLogMagnitude]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [localSignedLog_eq_neg_magnitude]
  simp

/-- The classical log is the negative of the actual q-pilot global log-volume. -/
theorem qPilotClassicalLog_eq_neg_globalLogVolume
    [Fintype (Bad (nativePlaceSelection X.S))] :
    qPilotClassicalLog X = - qPilotQGlobalLogVolume X := by
  rw [qPilotClassicalLog_eq_sum_localLogMagnitude,
    qPilotQGlobalLogVolume_eq_neg_sum_qVLogMagnitude]
  simp

end LeanFormal.IUT.XiFPaper.QPilotClassicalLogActual

end
