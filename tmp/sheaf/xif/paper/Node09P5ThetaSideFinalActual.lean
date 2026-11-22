import tmp.sheaf.xif.paper.Node09P5HullInequalityFinalActual
import tmp.sheaf.xif.paper.Node09P5ReadingBridgeActual
import tmp.sheaf.xif.paper.Mzk1P0QVFamNormBridgeDonorActual
import tmp.sheaf.xif.paper.GlobalQVFamThetaHullScalarActual
import Mathlib.Tactic

set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.Node09P5HullInequalityFinalActual
open LeanFormal.IUT.XiFPaper.Node09P5NormalizedRegionActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.Node09P5ReadingBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P0QVFamNormBridgeDonorActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

namespace LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [Fintype (Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S))]
variable [∀ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
  MeasurableSpace (qVFamTensorBlock X.S b)]
variable [∀ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
  BorelSpace (qVFamTensorBlock X.S b)]

/-- Actual theta-side reading: direct sum of the per-b qVFam theta-hull
normalized log-volumes. -/
noncomputable def qVFamThetaReading : Real :=
  ∑ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
    qVFamLocalThetaHullLogVolume X.S b

/-- Actual per-b qPilot <= theta-hull inequality summed over bad places. -/
theorem sum_qVFamNormalizedQPilotVolume_le_thetaReading :
    (∑ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
        qVFamNormalizedQPilotVolume X.S b) ≤ qVFamThetaReading X := by
  unfold qVFamThetaReading
  apply Finset.sum_le_sum
  intro b _
  simpa [qVFamLocalThetaHullLogVolume] using
    qVFamNormalizedQPilotVolume_le_thetaHullVolume X.S b

/-- Actual signed P5 inequality: qPilotRealifiedLogVolume <= theta-side reading,
using the summed inequality and the nonnegative norm-ratio correction. -/
theorem qPilotRealifiedLogVolume_le_thetaReading :
    qPilotRealifiedLogVolume X ≤ qVFamThetaReading X := by
  have hsum := sum_qVFamNormalizedQPilotVolume_eq_qPilot_add_ratio X
  have hle := sum_qVFamNormalizedQPilotVolume_le_thetaReading X
  have hcorr : 0 ≤ ∑ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
      Real.log (qVFamNormRatio X.S b) := by
    apply Finset.sum_nonneg
    intro b _
    exact Real.log_nonneg (Mzk1P0QVFamNormBridgeDonorActual.qVFamNormRatio_ge_one X.S b)
  rw [hsum] at hle
  linarith

#print axioms sum_qVFamNormalizedQPilotVolume_le_thetaReading
#print axioms qPilotRealifiedLogVolume_le_thetaReading

end LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual
end