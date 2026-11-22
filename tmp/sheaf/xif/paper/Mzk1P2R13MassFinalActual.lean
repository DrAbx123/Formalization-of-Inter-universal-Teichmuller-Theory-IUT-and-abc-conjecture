/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2RelativeMassActual
import tmp.sheaf.xif.paper.Mzk1P2R13vsC0RemainderActual
open LeanFormal.IUT.XiFPaper.Mzk1P2RelativeMassActual
open LeanFormal.IUT.XiFPaper.Mzk1P2R13vsC0RemainderActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open scoped BigOperators ENNReal

open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))]

theorem p2R13_nonneg : 0 ≤ p2RExact T := p2RExact_nonneg T

theorem p2R13_eq_neg_coeff :
    p2RExact T = -∑ b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T),
      (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : Real) *
        Real.log ‖p2Coefficient T b‖ := p2RExact_eq_neg_sum_log_coeff T

theorem p2R13_c0_diff :
    p2RExact T - c0RemainderV2 T = p2RExactCorrection T :=
  p2RExact_sub_c0RemainderV2_eq_correction T

end
