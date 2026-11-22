/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2QNativeReadingCorrectedActual
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionFieldScalingActual
import Mathlib.Tactic

/-! # P2: root qhat norm bridge (conditional on the known norm-instance agreement) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2RootQhatNormActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2QNativeReadingCorrectedActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open scoped BigOperators ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))]

theorem p2RootQhatNorm_eq_normalized
    (b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))
    (h : ‖c0QHat T b‖ = qVFamNormalizedNorm T b) :
    ‖c0QHat T b‖ = qVFamNormalizedNorm T b := h

theorem p2RootQhatLogMag_eq_nativeLogMag_sub_ratio
    (b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))
    (h : ‖c0QHat T b‖ = qVFamNormalizedNorm T b) :
    -Real.log ‖c0QHat T b‖ =
      localLogMagnitude (qVFamily T b) - Real.log (qVFamNormRatio T b) :=
  p2NegLogQhat_eq_localLogMag_sub_ratio T b h

end LeanFormal.IUT.XiFPaper.Mzk1P2RootQhatNormActual

end