/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
import tmp.sheaf.xif.paper.Mzk1P0NativeLSideActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeComparisonNonnegActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeLSideActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
theorem nativeLComparison_of_theta_nonneg_actual
    (h : 0 ≤ nativeLSideThetaReadout T b) : nativeLComparison T b :=
  le_trans (nativeQReadout_nonpos T b) h
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeComparisonNonnegActual
end