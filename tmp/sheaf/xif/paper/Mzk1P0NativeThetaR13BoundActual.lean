/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeThetaR13DefectActual
import tmp.sheaf.xif.paper.Mzk1P0NativeThetaR13ChainActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13BoundActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeLSideActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13BridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13DefectActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13ChainActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Defect is theta readout plus a nonpositive weighted det log. -/
theorem thetaR13Defect_eq_theta_add_weighted :
    thetaR13Defect T b =
      nativeLSideThetaReadout T b + p2WeightedDetLog T := rfl
/-- Actual upper bound: defect ≤ theta readout. -/
theorem thetaR13Defect_le_thetaReadout :
    thetaR13Defect T b ≤ nativeLSideThetaReadout T b := by
  rw [thetaR13Defect_eq_theta_add_weighted]
  have h : p2WeightedDetLog T ≤ 0 := p2WeightedDetLog_nonpos T
  linarith
/-- Nonnegative defect is a sufficient condition for native comparison. -/
theorem nativeComparison_of_defect_nonneg
    (h : 0 ≤ thetaR13Defect T b) : nativeLComparison T b := by
  have hw : p2WeightedDetLog T ≤ 0 := p2WeightedDetLog_nonpos T
  have htheta : 0 ≤ nativeLSideThetaReadout T b := by
    unfold thetaR13Defect at h
    linarith
  exact nativeLComparison_of_theta_nonneg T b htheta
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13BoundActual
end
