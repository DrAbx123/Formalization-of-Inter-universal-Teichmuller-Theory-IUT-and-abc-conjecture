/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import Mathlib.Tactic

/-! # A760 hull: explicit log-volume formulas for the root-extension hull

Formulas for the hull `fullRegion = s1902Hull = pi_b closedBall(0, rootImageRadius_b)`
and the unit region `s1902UnitRegion = pi_b closedBall(0,1)`:

* `log (productHaar hull).toReal = sum_b log (mu_b(ball(rootImageRadius_b))).toReal`;
* same for the unit region;
* `rootExtensionProductNormalizedLog hull = sum_b (log mu_ball_b - log mu_unit_b)`;
* `s1902LogVolume hull = ofReal (1 + normalizedLog hull)` (normalization factor `e`).

These are the hull-side half of the A760 log-volume dictionary; the lana-side
formulas (procession normalization, sFactor, theta-value radii) are abc's part.
No RETRACTED file referenced. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeFormulaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open MeasureTheory
open scoped ENNReal BigOperators NNReal Pointwise

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Product Haar of the hull is the product of the local closed-ball Haar masses. -/
theorem productHaar_hull_eq_prod_ball :
    rootExtensionProductHaar T (s1902Hull T) =
      ∏ b : Bad (nativePlaceSelection T),
        rootExtensionHaar T b
          (Metric.closedBall (0 : rootNormedExtension T b)
            ((rootImageRadius T b : NNReal) : Real)) := by
  unfold s1902Hull rootExtensionProductImageHull rootExtensionProductHaar
  rw [Measure.pi_pi]

/-- Product Haar of the unit region is the product of local unit-ball masses. -/
theorem productHaar_unit_eq_prod_ball :
    rootExtensionProductHaar T (s1902UnitRegion T) =
      ∏ b : Bad (nativePlaceSelection T),
        rootExtensionHaar T b (rootExtensionUnitBall T b) := by
  unfold s1902UnitRegion
  exact rootExtensionProductHaar_unitBall T

theorem localBall_toReal_pos (b : Bad (nativePlaceSelection T)) :
    0 < (rootExtensionHaar T b
      (Metric.closedBall (0 : rootNormedExtension T b)
        ((rootImageRadius T b : NNReal) : Real))).toReal := by
  refine ENNReal.toReal_pos (ne_of_gt ?_) (ne_of_lt ?_)
  · exact rootExtensionClosedBall_measure_pos (T := T) (b := b) _
      (by exact_mod_cast rootImageRadius_pos (T := T) (b := b))
  · exact rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _

theorem localUnit_toReal_pos (b : Bad (nativePlaceSelection T)) :
    0 < (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal :=
  ENNReal.toReal_pos (ne_of_gt (rootExtensionUnitBall_measure_pos T b))
    (ne_of_lt (rootExtensionUnitBall_measure_lt_top T b))

/-- Log of the hull's product Haar mass is the sum of the local log-masses. -/
theorem productHaar_hull_log :
    Real.log (rootExtensionProductHaar T (s1902Hull T)).toReal =
      ∑ b : Bad (nativePlaceSelection T),
        Real.log (rootExtensionHaar T b
          (Metric.closedBall (0 : rootNormedExtension T b)
            ((rootImageRadius T b : NNReal) : Real))).toReal := by
  rw [productHaar_hull_eq_prod_ball T, ENNReal.toReal_prod, Real.log_prod]
  intro b _
  exact (localBall_toReal_pos T b).ne'

/-- Log of the unit region's product Haar mass is the sum of local unit logs. -/
theorem productHaar_unit_log :
    Real.log (rootExtensionProductHaar T (s1902UnitRegion T)).toReal =
      ∑ b : Bad (nativePlaceSelection T),
        Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal := by
  rw [productHaar_unit_eq_prod_ball T, ENNReal.toReal_prod, Real.log_prod]
  intro b _
  exact (localUnit_toReal_pos T b).ne'

/-- Log of the unit-ball product Haar mass (unit-ball spelling). -/
theorem productHaar_unitBall_log :
    Real.log (rootExtensionProductHaar T (rootExtensionProductUnitBall T)).toReal =
      ∑ b : Bad (nativePlaceSelection T),
        Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal := by
  rw [rootExtensionProductHaar_unitBall T, ENNReal.toReal_prod, Real.log_prod]
  intro b _
  exact (localUnit_toReal_pos T b).ne'

/-- **Normalized hull log** as a sum of local ratios. -/
theorem normalizedLog_hull_eq_sum_diff :
    rootExtensionProductNormalizedLog T (s1902Hull T) =
      ∑ b : Bad (nativePlaceSelection T),
        (Real.log (rootExtensionHaar T b
            (Metric.closedBall (0 : rootNormedExtension T b)
              ((rootImageRadius T b : NNReal) : Real))).toReal -
          Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal) := by
  unfold rootExtensionProductNormalizedLog
  rw [productHaar_hull_log T, productHaar_unitBall_log T]
  rw [← Finset.sum_sub_distrib]

/-- The normalized measure of a set `S` at the level of `toReal`. -/
theorem s1902NormalizedHaar_apply_toReal (S : Set (S1902Carrier T)) :
    (s1902NormalizedHaar T S).toReal =
      Real.exp 1 * (rootExtensionProductHaar T S).toReal /
        (rootExtensionProductHaar T (s1902UnitRegion T)).toReal := by
  unfold s1902NormalizedHaar s1902HaarScale
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  simp only [s1902UnitRegion]
  ring_nf

/-- **The `s1902` log-volume of the hull** in terms of the normalized log. -/
theorem s1902LogVolume_hull_eq_normalized :
    s1902LogVolume T (s1902Hull T) =
      ENNReal.ofReal (1 + rootExtensionProductNormalizedLog T (s1902Hull T)) := by
  unfold s1902LogVolume
  have hfin : s1902NormalizedHaar T (s1902Hull T) < ⊤ := by
    unfold s1902NormalizedHaar
    rw [Measure.smul_apply]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (rootExtensionProductImageHull_measure_pos_lt_top (T := T)).2
  rw [haarLogVolume_of_lt_top hfin, s1902NormalizedHaar_apply_toReal T]
  congr 1
  unfold rootExtensionProductNormalizedLog
  have hP : 0 < (rootExtensionProductHaar T (s1902Hull T)).toReal := by
    rw [productHaar_hull_eq_prod_ball T, ENNReal.toReal_prod]
    exact Finset.prod_pos fun b _ => localBall_toReal_pos T b
  have hU : 0 < (rootExtensionProductHaar T (s1902UnitRegion T)).toReal := by
    rw [show (s1902UnitRegion T) = rootExtensionProductUnitBall T from rfl,
      rootExtensionProductHaar_unitBall T, ENNReal.toReal_prod]
    exact Finset.prod_pos fun b _ => localUnit_toReal_pos T b
  simp only [s1902UnitRegion] at *
  rw [Real.log_div (mul_ne_zero (Real.exp_pos 1).ne' hP.ne') hU.ne',
    Real.log_mul (Real.exp_pos 1).ne' hP.ne', Real.log_exp]
  rw [productHaar_hull_log T, productHaar_unitBall_log T]
  ring

def dictionaryRows : List (String × String × String) :=
  [ ("hull volume", "log(productHaar hull).toReal = sum_b log mu_b(closedBall rootImageRadius_b)", "productHaar_hull_log"),
    ("unit volume", "log(productHaar unit).toReal = sum_b log mu_b(unitBall)", "productHaar_unit_log"),
    ("normalized hull log", "normalizedLog hull = sum_b (log mu_ball_b - log mu_unit_b)", "normalizedLog_hull_eq_sum_diff"),
    ("s1902 hull log-volume", "s1902LogVolume hull = ofReal(1 + normalizedLog hull)", "s1902LogVolume_hull_eq_normalized"),
    ("unit normalization", "s1902LogVolume unit = 1 (green S1902)", "s1902LogVolume_unitRegion"),
    ("bridge gap", "identify rootImageRadius_b with lana theta-value radii and normalizedLog with lana logVol(hull(vcI)); needs lana local-volume formula", "abc side") ]

theorem dictionaryRows_length : dictionaryRows.length = 6 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeFormulaActual.productHaar_hull_log
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeFormulaActual.normalizedLog_hull_eq_sum_diff
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeFormulaActual.s1902LogVolume_hull_eq_normalized

end LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeFormulaActual

end