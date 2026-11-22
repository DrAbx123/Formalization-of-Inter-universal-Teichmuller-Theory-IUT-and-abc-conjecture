/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
import tmp.sheaf.xif.paper.Mzk1P0NativeLSideActual
import tmp.sheaf.xif.paper.Mzk1P0NativeQDonorActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeQBridgeProofActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeLSideActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeQDonorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
theorem nativeLCarrier_q_bridge :
    nativeLSideQReadout T b = nativeQReadout T b := rfl
theorem nativeLCarrier_q_donor :
    nativeLSideQReadout T b = donorQReadout T b := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeQBridgeProofActual
end
