/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ThetaRootCarrierActual
import tmp.sheaf.xif.paper.Mzk1NativeNormalizedUnitMassConditionalActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import Mathlib.Tactic

/-! # #10: unit ball and product Haar on the correct root carrier -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaRootCarrierHaarActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1ThetaRootCarrierActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1NativeNormalizedUnitMassConditionalActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem thetaRootCarrier_unitBall_mem_iff (x : ThetaRootCarrier T) :
    x ∈ rootExtensionProductUnitBall T ↔
      thetaRootCarrierEquiv T x ∈ rootExtensionProductUnitBall T := Iff.rfl

theorem thetaRootCarrier_productHaar_eq :
    (Measure.pi (fun b => rootExtensionHaar T b) : Measure (ThetaRootCarrier T)) =
      rootExtensionProductHaar T := rfl

theorem thetaRootCarrier_normalizedUnitMass_eq_one
    [∀ b, SigmaFinite (normalizedRootExtensionHaar T b)] :
    (normalizedProduct T (rootExtensionProductUnitBall T)).toReal = 1 := by
  rw [normalizedProduct_unitBall]
  norm_num

end LeanFormal.IUT.XiFPaper.Mzk1ThetaRootCarrierHaarActual
