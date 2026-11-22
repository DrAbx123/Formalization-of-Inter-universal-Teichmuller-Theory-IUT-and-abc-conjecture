/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeComparisonR13Actual
import tmp.sheaf.xif.paper.Mzk1P2DetWeightedNonnegActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13BridgeActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeLSideActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeComparisonR13Actual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Exact interface: native L theta readout equals the P2 R1.3 mass difference. -/
def ThetaR13Bridge : Prop := nativeLSideThetaReadout T b = p2R13Exact T
/-- Equivalent weighted form of the bridge. -/
theorem thetaR13Bridge_iff_weighted :
    ThetaR13Bridge T b ↔ nativeLSideThetaReadout T b = -p2WeightedDetLog T := by
  unfold ThetaR13Bridge
  rw [p2R13Exact_eq_neg_p2WeightedDetLog]
/-- The R1.3 interface gives the native comparison. -/
theorem nativeComparison_of_thetaR13Bridge (h : ThetaR13Bridge T b) :
    nativeLComparison T b :=
  nativeLComparison_of_theta_eq_R13 T b h
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13BridgeActual
end
