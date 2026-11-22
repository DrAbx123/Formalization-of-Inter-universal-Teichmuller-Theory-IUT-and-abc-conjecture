/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ThetaRootCarrierActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import Mathlib.Tactic

/-! # #10: unit-ball transport on the correct root carrier -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaRootUnitBallTransportActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1ThetaRootCarrierActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem thetaRootCarrierEquiv_image_unitBall :
    thetaRootCarrierEquiv T '' rootExtensionProductUnitBall T =
      rootExtensionProductUnitBall T := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [thetaRootCarrierEquiv] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem thetaRootCarrierEquiv_preimage_unitBall :
    thetaRootCarrierEquiv T ⁻¹' rootExtensionProductUnitBall T =
      rootExtensionProductUnitBall T := by
  ext x
  exact Iff.rfl

end LeanFormal.IUT.XiFPaper.Mzk1ThetaRootUnitBallTransportActual
