/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NativeNormalizedUnitMassConditionalActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import Mathlib.Tactic

/-! # #10: explicit actual unitMass factor c = ∏ local unit-ball masses -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1NativeUnitMassActualFactorActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1NativeNormalizedUnitMassConditionalActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual (unnormalized) product unit mass, i.e. `s1915UnitMass`. -/
noncomputable def actualUnitMassENN : ℝ≥0∞ :=
  rootExtensionProductHaar T (rootExtensionProductUnitBall T)

theorem actualUnitMassENN_eq_prod_rootUnitMass
    [∀ b, SigmaFinite (rootExtensionHaar T b)] :
    actualUnitMassENN (T := T) = ∏ b, rootUnitMass (T := T) b := by
  unfold actualUnitMassENN rootExtensionProductHaar rootExtensionProductUnitBall rootUnitMass
  rw [Measure.pi_pi]

theorem actualUnitMassENN_toReal_eq_prod
    [∀ b, SigmaFinite (rootExtensionHaar T b)] :
    (actualUnitMassENN (T := T)).toReal = ∏ b, (rootUnitMass (T := T) b).toReal := by
  rw [actualUnitMassENN_eq_prod_rootUnitMass, ENNReal.toReal_prod]

theorem actualUnitMassENN_eq_one_iff_prod
    [∀ b, SigmaFinite (rootExtensionHaar T b)] :
    actualUnitMassENN (T := T) = 1 ↔ ∏ b, rootUnitMass (T := T) b = 1 := by
  rw [actualUnitMassENN_eq_prod_rootUnitMass]

def unitMassFactorRows : List (String × String) :=
  [ ("actualUnitMassENN_eq_prod_rootUnitMass", "conditional on SigmaFinite: explicit c=∏c_b"),
    ("actualUnitMassENN_toReal_eq_prod", "explicit real factor"),
    ("actualUnitMassENN=1 iff ∏c_b=1", "exact condition; c_b product not known 1") ]
theorem unitMassFactorRows_length : unitMassFactorRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NativeUnitMassActualFactorActual
