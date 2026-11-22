import tmp.sheaf.n8.closure.EtaQOAddHaarNormalizedCalibrationActual
import tmp.sheaf.n8.closure.EtaGlobalRegionAtFActual
import Mathlib

/-!
# Kf closed ball equals qO region

In the spectral-norm Kf carrier, the actual qO region of a nonzero q is the
closed ball of radius ||q||.  The proof uses the nonarchimedean local-field
Integers membership criterion and multiplicativity of the norm.  No arbitrary
transport is used.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField

namespace LeanFormal.IUT.N8Closure.EtaKfClosedBallEqQORegion

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

/-- The spectral-norm Kf carrier, as a function of X. -/
abbrev KF (X : N8NativeInput l) : Type :=
  EtaGeneralQHaarScalingActual.Kf X

/-- Actual qO region of a general nonzero q is the closed ball of radius ||q||. -/
theorem kf_qORegion_eq_closedBall (q : (KF X)ˣ) :
    qORegion X (q : KF X) =
      Metric.closedBall (0 : KF X) ‖(q : KF X)‖ := by
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_mul]
    have hy : ‖(y : KF X)‖ ≤ 1 :=
      (mem_integers_iff (K := KF X) _).mp y.2
    calc
      ‖(q : KF X)‖ * ‖(y : KF X)‖
          ≤ ‖(q : KF X)‖ * 1 :=
        mul_le_mul_of_nonneg_left hy (norm_nonneg _)
      _ = ‖(q : KF X)‖ := mul_one _
  · intro hx
    have hq : (q : KF X) ≠ 0 := Units.ne_zero q
    refine ⟨⟨x / (q : KF X), ?_⟩, ?_⟩
    · rw [mem_integers_iff (K := KF X)]
      have hxle : ‖x‖ ≤ ‖(q : KF X)‖ := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      rw [norm_div, div_le_one (norm_pos_iff.mpr hq)]
      exact hxle
    · field_simp [hq]
      simp

/-- The normalized Haar mass of the same closed ball is ||q||^d. -/
theorem kfNormalizedHaar_closedBall_toReal (q : (KF X)ˣ) :
    (EtaQOAddHaarNormalizedCalibrationActual.kfNormalizedHaar X
      (Metric.closedBall (0 : KF X) ‖(q : KF X)‖)).toReal =
      ‖(q : KF X)‖ ^ Module.finrank ℚ_[nativePrime X] (KF X) := by
  rw [← kf_qORegion_eq_closedBall (X := X) q]
  exact EtaQOAddHaarNormalizedCalibrationActual.kfNormalizedHaar_qORegion_toReal
    (X := X) q

end LeanFormal.IUT.N8Closure.EtaKfClosedBallEqQORegion
