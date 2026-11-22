/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeThetaR13DefectActual
import tmp.sheaf.xif.paper.Mzk1P2DetWeightedNonnegActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13ChainActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeLSideActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13BridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13DefectActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
theorem nativeComparison_of_thetaR13Defect_zero
    (h : thetaR13Defect T b = 0) : nativeLComparison T b :=
  nativeComparison_of_thetaR13Bridge T b
    ((thetaR13Bridge_iff_defect_zero T b).mpr h)
theorem nativeComparison_of_R13_defect_sign
    (h : 0 ≤ thetaR13Defect T b) : nativeLComparison T b := by
  have htheta : 0 ≤ nativeLSideThetaReadout T b := by
    unfold thetaR13Defect at h
    have hw : p2WeightedDetLog T ≤ 0 := p2WeightedDetLog_nonpos T
    linarith
  exact nativeLComparison_of_theta_nonneg T b htheta
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13ChainActual
end
