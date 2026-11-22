/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeLSideActual
import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutPairActual
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
theorem nativeReadoutPair_eq :
    (nativeLSideQReadout T b, nativeLSideThetaReadout T b) =
      (nativeQReadout T b, nativeThetaReadout T b) := by
  rw [nativeLSideQReadout_eq, nativeLSideThetaReadout_eq]
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutPairActual
end
