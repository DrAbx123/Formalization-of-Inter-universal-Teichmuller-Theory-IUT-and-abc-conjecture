/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open scoped BigOperators ENNReal

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))]

theorem p2NormGenerator_norm (b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) :
    ‖qVFamNormalizedGenerator T b‖ =
      (qVFamTensorP T b : Real) ^ (-(qVFamNormalizedCoefficient T b)) :=
  qVFamNormalizedGenerator_norm T b

theorem p2NormGenerator_coeff_pos (b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) :
    0 < qVFamNormalizedCoefficient T b := qVFamNormalizedCoefficient_pos T b

end
