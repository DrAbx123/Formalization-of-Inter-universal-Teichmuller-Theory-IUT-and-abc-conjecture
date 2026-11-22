/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NativeUnitMassActualFactorActual
import Mathlib.Tactic

/-! # #10: explicit factor c = ∏ c_b, positivity, normalized scalar = 1 -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1NativeUnitMassNormalizedProofActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1NativeNormalizedUnitMassConditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1NativeUnitMassActualFactorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Positivity of the explicit factor c = ∏ local unit-ball masses. -/
theorem unitMassFactor_pos : 0 < ∏ b, rootUnitMass (T := T) b := by
  classical
  induction (Finset.univ : Finset (Bad (nativePlaceSelection T))) using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact ENNReal.mul_pos (ne_of_gt (rootExtensionUnitBall_measure_pos (T := T) (b := a))) (ne_of_gt ih)

/-- Finiteness of the explicit factor c. -/
theorem unitMassFactor_lt_top : (∏ b, rootUnitMass (T := T) b) < ⊤ := by
  exact ENNReal.prod_lt_top (fun b _ => rootExtensionUnitBall_measure_lt_top (T := T) (b := b))

/-- Normalized scalar: c⁻¹ * actual unit mass = 1. -/
theorem normalizedUnitMassScalar_eq_one
    (hSigma : ∀ b, SigmaFinite (rootExtensionHaar T b)) :
    (∏ b, rootUnitMass (T := T) b)⁻¹ * actualUnitMassENN (T := T) = 1 := by
  haveI := hSigma
  rw [actualUnitMassENN_eq_prod_rootUnitMass]
  exact ENNReal.inv_mul_cancel (ne_of_gt (unitMassFactor_pos T))
    (ne_of_lt (unitMassFactor_lt_top T))

def rows : List (String × String) :=
  [ ("unitMassFactor_pos", "new proof"),
    ("unitMassFactor_lt_top", "new proof"),
    ("normalizedUnitMassScalar_eq_one", "new proof: c⁻¹*actual=1") ]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NativeUnitMassNormalizedProofActual
