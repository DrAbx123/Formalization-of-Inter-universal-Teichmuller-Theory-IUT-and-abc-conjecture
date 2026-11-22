/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ThetaRootCarrierActual
import tmp.sheaf.xif.paper.Mzk1NativeNormalizedUnitMassConditionalActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import Mathlib.Tactic

/-! # #10: normalized unit mass = 1 on the correct root carrier -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaRootNormalizedUnitMassActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1ThetaRootCarrierActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1NativeNormalizedUnitMassConditionalActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem thetaRoot_normalizedProduct_unitBall
    [∀ b, SigmaFinite (normalizedRootExtensionHaar T b)] :
    normalizedProduct T (rootExtensionProductUnitBall T) = 1 := by
  unfold normalizedProduct rootExtensionProductUnitBall
  rw [Measure.pi_pi]
  simp [normalizedRootExtensionHaar_unitBall]

theorem thetaRoot_normalizedUnitMass_eq_one
    [∀ b, SigmaFinite (normalizedRootExtensionHaar T b)] :
    (normalizedProduct T (rootExtensionProductUnitBall T)).toReal = 1 := by
  rw [thetaRoot_normalizedProduct_unitBall]
  norm_num

end LeanFormal.IUT.XiFPaper.Mzk1ThetaRootNormalizedUnitMassActual
