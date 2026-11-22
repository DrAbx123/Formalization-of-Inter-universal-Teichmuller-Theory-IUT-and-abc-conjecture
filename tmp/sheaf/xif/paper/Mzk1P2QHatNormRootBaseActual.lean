/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2QHatNormAgreementUnconditionalActual
import Mathlib.Tactic

/-! # A2/P2: root-base norm status (donor obsolete; exact equivalence only) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2QHatNormRootBaseActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2QHatNormAgreementUnconditionalActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open scoped BigOperators ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))]

theorem p2QHat_normStandard_iff_ratio_one
    (b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) :
    (qVFamNormalizedNorm T b = qVFamDefaultNorm T b) ↔ qVFamNormRatio T b = 1 :=
  p2QHatNormStandardAgreement_iff_ratio_one T b

theorem p2QNativeReading_defaultNorm_re
    (b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) :
    localLogMagnitude (qVFamily T b) = -Real.log (qVFamDefaultNorm T b) :=
  p2QNativeReading_defaultNorm T b

end LeanFormal.IUT.XiFPaper.Mzk1P2QHatNormRootBaseActual

end