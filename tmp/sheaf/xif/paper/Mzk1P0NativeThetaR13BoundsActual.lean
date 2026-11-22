/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeThetaR13BoundActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13BoundsActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeLSideActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13BoundActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Under nonnegative defect, q readout is bounded above by defect. -/
theorem qReadout_le_thetaR13Defect_of_nonneg
    (h : 0 ≤ thetaR13Defect T b) : nativeLSideQReadout T b ≤ thetaR13Defect T b :=
  le_trans (nativeQReadout_nonpos T b) h
/-- Two-sided chain: qReadout ≤ defect ≤ thetaReadout. -/
theorem qReadout_le_thetaReadout_of_defect_nonneg
    (h : 0 ≤ thetaR13Defect T b) : nativeLSideQReadout T b ≤ nativeLSideThetaReadout T b := by
  have h1 : nativeLSideQReadout T b ≤ thetaR13Defect T b :=
    qReadout_le_thetaR13Defect_of_nonneg T b h
  have h2 : thetaR13Defect T b ≤ nativeLSideThetaReadout T b :=
    thetaR13Defect_le_thetaReadout T b
  exact le_trans h1 h2
/-- Lower bound on theta readout in terms of defect: thetaReadout ≥ defect. -/
theorem thetaReadout_ge_thetaR13Defect :
    thetaR13Defect T b ≤ nativeLSideThetaReadout T b :=
  thetaR13Defect_le_thetaReadout T b
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13BoundsActual
end
