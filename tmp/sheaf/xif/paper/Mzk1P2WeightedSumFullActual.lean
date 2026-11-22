/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2WeightedSumActual
import tmp.sheaf.xif.paper.Mzk1P2LabelBlockCoefficientActual
import tmp.sheaf.xif.paper.Mzk1P2RelativeMassActual
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeV2Actual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P2WeightedSumActual
open LeanFormal.IUT.XiFPaper.Mzk1P2RelativeMassActual
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open scoped BigOperators ENNReal

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))]

theorem p2WeightedSum_RExact :
    p2RExact T = p2WeightedLogLambda T - p2WeightedLogQhat T :=
  p2RExact_eq_weighted_sub T

theorem p2WeightedSum_coeff :
    p2WeightedLogQhat T - p2WeightedLogLambda T =
      ∑ b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T),
        (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : Real) *
          Real.log ‖p2Coefficient T b‖ :=
  p2WeightedLogQhat_sub_lambda_eq_sum_log_coeff T

end
