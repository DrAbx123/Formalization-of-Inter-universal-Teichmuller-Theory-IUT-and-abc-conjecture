/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NativeUnitMassNormalizedProofActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.Mzk1ThetaRootCarrierActual
import Mathlib.Tactic

/-! # #10: root product unit-ball mass citizen and its normalization -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1RootUnitMassCitizenActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaRootCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1NativeUnitMassNormalizedProofActual
open LeanFormal.IUT.XiFPaper.Mzk1NativeNormalizedUnitMassConditionalActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual product unit-ball mass on the correct root carrier. -/
noncomputable def rootUnitBallMass : ℝ≥0∞ :=
  rootExtensionProductHaar T (rootExtensionProductUnitBall T)

theorem rootUnitBallMass_pos : 0 < rootUnitBallMass (T := T) := by
  exact (rootExtensionProductHaar_unitBall_pos_lt_top (T := T)).1

theorem rootUnitBallMass_lt_top : rootUnitBallMass (T := T) < ⊤ := by
  exact (rootExtensionProductHaar_unitBall_pos_lt_top (T := T)).2

theorem rootUnitBallMass_ne_zero : rootUnitBallMass (T := T) ≠ 0 :=
  ne_of_gt (rootUnitBallMass_pos (T := T))

theorem rootUnitBallMass_ne_top : rootUnitBallMass (T := T) ≠ ⊤ :=
  ne_of_lt (rootUnitBallMass_lt_top (T := T))

/-- Normalized citizen: dividing the root-product unit-ball mass by itself gives 1. -/
theorem normalizedRootUnitBallMass_eq_one :
    (rootUnitBallMass (T := T))⁻¹ * rootUnitBallMass (T := T) = 1 :=
  ENNReal.inv_mul_cancel (rootUnitBallMass_ne_zero (T := T))
    (rootUnitBallMass_ne_top (T := T))

/-- The root-product unit-ball mass is exactly the explicit factor c = ∏ c_b. -/
theorem rootUnitBallMass_eq_prod_rootUnitMass
    [∀ b, SigmaFinite (rootExtensionHaar T b)] :
    rootUnitBallMass (T := T) = ∏ b, rootUnitMass (T := T) b := by
  unfold rootUnitBallMass rootExtensionProductHaar rootExtensionProductUnitBall
  rw [Measure.pi_pi]
  rfl

end LeanFormal.IUT.XiFPaper.Mzk1RootUnitMassCitizenActual
