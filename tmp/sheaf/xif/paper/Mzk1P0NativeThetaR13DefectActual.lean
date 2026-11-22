/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeThetaR13BridgeActual
import tmp.sheaf.xif.paper.Mzk1P2DetWeightedNonnegActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13DefectActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeLSideActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13BridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Exact defect certificate: theta readout plus the P2 weighted det log. -/
noncomputable def thetaR13Defect : Real :=
  nativeLSideThetaReadout T b + p2WeightedDetLog T
theorem thetaR13Bridge_iff_defect_zero :
    ThetaR13Bridge T b ↔ thetaR13Defect T b = 0 := by
  unfold ThetaR13Bridge thetaR13Defect
  rw [p2R13Exact_eq_neg_p2WeightedDetLog]
  constructor
  · intro h; linarith
  · intro h; linarith
theorem thetaR13Defect_eq_add :
    thetaR13Defect T b = nativeLSideThetaReadout T b + p2WeightedDetLog T := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13DefectActual
end
