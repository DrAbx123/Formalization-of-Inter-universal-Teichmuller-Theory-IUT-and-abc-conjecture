/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullLogVolumeFormulaActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import Mathlib.Tactic
/-! # GAP-P7-HULL-UB B6: raw paper V binding -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperVRawBindingActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeFormulaActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
instance badNonempty : Nonempty (Bad (nativePlaceSelection T)) := by
  rcases (nativePlaceSelection T).V_mod_bad_nonempty with ⟨p, hp⟩
  exact ⟨⟨p, hp⟩⟩
theorem closedForm_eq_one_add_normalizedLog :
    s1915ClosedForm T =
      1 + rootExtensionProductNormalizedLog T (s1902Hull T) := by
  rw [← s1915_log_normalized_hull]
  have h := s1902NormalizedHaar_apply_toReal (T := T) (s1902Hull T)
  rw [h]
  have hApos : 0 < (rootExtensionProductHaar T (s1902Hull T)).toReal := by
    rw [productHaar_hull_eq_prod_ball T, ENNReal.toReal_prod]
    exact Finset.prod_pos fun b _ => localBall_toReal_pos T b
  have hUpos : 0 < (rootExtensionProductHaar T (s1902UnitRegion T)).toReal := by
    rw [show s1902UnitRegion T = rootExtensionProductUnitBall T from rfl,
      rootExtensionProductHaar_unitBall T, ENNReal.toReal_prod]
    exact Finset.prod_pos fun b _ => localUnit_toReal_pos T b
  rw [Real.log_div (mul_ne_zero (Real.exp_pos 1).ne' hApos.ne') hUpos.ne',
    Real.log_mul (Real.exp_pos 1).ne' hApos.ne', Real.log_exp]
  unfold rootExtensionProductNormalizedLog
  simp only [s1902UnitRegion]
  ring
theorem paperV_eq_sum_add_beta :
    s1915ClosedForm T = 1 + ∑ b : Bad (nativePlaceSelection T),
      (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real) := rfl
def rows : List String := ["rawV := s1915ClosedForm", "rawV = 1 + normalizedLog", "rawV = 1 + sum d_b log r_b", "B6 binding"]
theorem rows_length : rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperVRawBindingActual
end