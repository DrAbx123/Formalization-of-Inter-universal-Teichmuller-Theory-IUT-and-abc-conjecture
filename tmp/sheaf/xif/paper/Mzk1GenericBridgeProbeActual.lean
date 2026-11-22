/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GeneralNormalizedNormBySpectralUniqueness
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.Mzk1GenericBridgeProbeActual
open LeanFormal.IUT LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.GeneralNormalizedNormBySpectralUniqueness
universe u
variable {F : Type u} [Field F] [NumberField F] (place : NumberField.FinitePlace F)
def defaultNormedField : NormedField (NormalizedCompletion place) :=
  Valued.toNormedField (NormalizedCompletion place) (WithZero (Multiplicative ℤ))
theorem normalized_norm_eq_default_norm_rpow
    (x : NormalizedCompletion place) (hx : x ≠ 0) :
    @norm (NormalizedCompletion place)
        (normalizedCompletionNontriviallyNormedField place).toNorm x =
      (@norm (NormalizedCompletion place) (defaultNormedField place).toNorm x) ^
        (1 / (relativeCompletionDegree (k := ℚ) place : ℝ)) := by
  have hnorm := generalNormalizedNormFormula (F := F) place x
  have hdef := @norm_eq_absNorm_zpow F _ _ place x hx
  have hv : Valued.v (toC place x) ≠ 0 := valuation_ne_zero_of_ne_zero place (toC place x) (by simpa [toC_apply] using hx)
  have hlog : WithZero.log (Valued.v (toC place x)) =
      Multiplicative.toAdd (WithZero.unzero hv) := by
    conv_lhs => rw [← WithZero.coe_unzero hv]
    rfl
  have hnu : nu place x = -Multiplicative.toAdd (WithZero.unzero hv) := by
    unfold nu
    rw [hlog]
  have hval : Multiplicative.toAdd (WithZero.unzero hv) = -nu place x := by
    rw [hnu]; ring
  rw [hnorm hx, hdef, hval]
  rw [← Real.rpow_mul (le_of_lt (lt_trans zero_lt_one (absNorm_gt_one place)))]
  congr 1
  ring
end LeanFormal.IUT.XiFPaper.Mzk1GenericBridgeProbeActual
end