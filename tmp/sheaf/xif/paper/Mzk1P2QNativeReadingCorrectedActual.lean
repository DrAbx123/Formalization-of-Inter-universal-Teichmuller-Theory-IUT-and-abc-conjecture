/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeV2Actual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import Mathlib.Tactic

/-! # P2: q reading sign correction up to the known norm-instance gap -/

/-
| field | value |
|---|---|
| Status | PROVED: `localLogMagnitude(qVFamily) = -log‖c0QHat‖ + log(qVFamNormRatio)` **conditional on the norm-instance agreement** `‖c0QHat‖=qVFamNormalizedNorm`; the old sign statement `-log‖qhat‖=localLogMagnitude` is false unless ratio=1 |
| GAP | `P2QHatNormInstanceAgreement` (`‖c0QHat T b‖ = qVFamNormalizedNorm T b`) is an **independent c0QHat norm-instance coherence**, NOT equivalent to `qVFamNormRatio=1` (the S45 source condition). Do not merge the two conditions. |
-/

noncomputable section
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P2QNativeReadingCorrectedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open scoped BigOperators ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))]

/-- The exact norm-instance agreement needed for the sign bridge. -/
def P2QHatNormInstanceAgreement : Prop :=
  ∀ b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T),
    ‖c0QHat T b‖ = qVFamNormalizedNorm T b

/-- Corrected reading relation: `localLogMagnitude = -log‖qhat‖ + log ratio`
under the norm-instance agreement. -/
theorem p2NativeQReading_eq_neg_log_qhat_add_ratio
    (b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))
    (h : ‖c0QHat T b‖ = qVFamNormalizedNorm T b) :
    localLogMagnitude (qVFamily T b) =
      -Real.log ‖c0QHat T b‖ + Real.log (qVFamNormRatio T b) := by
  have h1 := qVFamNormalizedCoefficient_mul_log_eq_neg_log_norm (T := T) (b := b)
  have h2 := qVFamNormalizedCoefficient_mul_log_eq_localLogMagnitude_sub_log_ratio (T := T) (b := b)
  have hlog : Real.log ‖c0QHat T b‖ = Real.log (qVFamNormalizedNorm T b) := by rw [h]
  linarith [h1, h2, hlog]

/-- Unconditional form (under the agreement): `localLogMagnitude(q) - log ratio = -log‖qhat‖`. -/
theorem p2NegLogQhat_eq_localLogMag_sub_ratio
    (b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))
    (h : ‖c0QHat T b‖ = qVFamNormalizedNorm T b) :
    -Real.log ‖c0QHat T b‖ =
      localLogMagnitude (qVFamily T b) - Real.log (qVFamNormRatio T b) := by
  rw [p2NativeQReading_eq_neg_log_qhat_add_ratio T b h]
  ring

end LeanFormal.IUT.XiFPaper.Mzk1P2QNativeReadingCorrectedActual

end