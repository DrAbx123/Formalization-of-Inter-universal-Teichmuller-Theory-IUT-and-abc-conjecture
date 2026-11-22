/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeLSideActual
import tmp.sheaf.xif.paper.Mzk1P2DetWeightedNonnegActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeComparisonR13Actual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeLSideActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
theorem p2R13Exact_nonneg_bridge : 0 ≤ p2R13Exact T := p2R13Exact_nonneg T
theorem nativeLComparison_of_theta_eq_R13
    (h : nativeLSideThetaReadout T b = p2R13Exact T) : nativeLComparison T b := by
  have hnonneg : 0 ≤ nativeLSideThetaReadout T b := by
    rw [h]; exact p2R13Exact_nonneg T
  exact nativeLComparison_of_theta_nonneg T b hnonneg
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeComparisonR13Actual
end
