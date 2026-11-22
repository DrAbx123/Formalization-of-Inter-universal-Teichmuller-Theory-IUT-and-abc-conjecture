import tmp.sheaf.n8.closure.EtaFPlaceSignedComparison
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-!
# Eta signed criterion: production arithmetic form

The corrected signed comparison is

  fPlaceLogVolume = -fPlaceNormalizedQVolume.

Its exact criterion was fPlaceVolumeIndex = exp(qPilotLogMagnitude).  Using the
production formula
  qPilotLogMagnitude = order * log(residueNormBase),
we prove

  exp(qPilotLogMagnitude) = residueNormBase ^ order,

so the criterion is exactly the arithmetic equation

  fPlaceVolumeIndex = residueNormBase (native F-place) ^ order.

This is a concrete production formula; no arbitrary sign.  The equation is not
decided globally by the current data, so we record the exact criterion and the
partial no-go at index 1.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaSignedCriterionDisproof

open scoped Padic

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open LeanFormal.IUT.N8Closure.EtaFPlaceComparisonProof
open LeanFormal.IUT.N8Closure.EtaFPlaceSignedComparison
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange

variable {l : PrimeGeFive}
variable {X : N8NativeInput l}

/-- Production arithmetic form of exp(qPilotLogMagnitude). -/
theorem exp_qPilotLogMagnitude_eq_residueNormBase_pow_order
    (X : N8NativeInput l) :
    Real.exp (qPilotLogMagnitude X) =
      ArithmeticQPilotBaseChange.residueNormBase (nativeFPlaceOverBad X) ^
        (C9QPilotRegion.nativeQ X).order := by
  rw [qPilotLogMagnitude]
  rw [ArithmeticQPilotBaseChange.localLogMagnitude_eq_order_mul_log (C9QPilotRegion.nativeQ X)]
  rw [Real.exp_nat_mul]
  rw [Real.exp_log (lt_trans zero_lt_one
    (ArithmeticQPilotBaseChange.residueNormBase_gt_one (nativeFPlaceOverBad X)))]

/-- Exact arithmetic criterion for the corrected signed comparison. -/
theorem signedCriterion_iff_index_eq_residueNormBase_pow
    (X : N8NativeInput l) :
    EtaFPlaceSignedComparisonTarget X ↔
      fPlaceVolumeIndex X =
        ArithmeticQPilotBaseChange.residueNormBase (nativeFPlaceOverBad X) ^
          (C9QPilotRegion.nativeQ X).order := by
  rw [signedComparison_iff_index_exp_magnitude]
  rw [exp_qPilotLogMagnitude_eq_residueNormBase_pow_order]

/-- The exact criterion forces volumeIndex > 1: the residue norm base is > 1
and the q order is positive. -/
theorem signedCriterion_implies_index_gt_one
    (X : N8NativeInput l)
    (h : EtaFPlaceSignedComparisonTarget X) :
    1 < fPlaceVolumeIndex X := by
  rw [signedCriterion_iff_index_eq_residueNormBase_pow] at h
  have hbase : 1 < ArithmeticQPilotBaseChange.residueNormBase (nativeFPlaceOverBad X) :=
    ArithmeticQPilotBaseChange.residueNormBase_gt_one (nativeFPlaceOverBad X)
  have hpow_gt_one : 1 <
      ArithmeticQPilotBaseChange.residueNormBase (nativeFPlaceOverBad X) ^
        (C9QPilotRegion.nativeQ X).order := by
    have horder : 0 < (C9QPilotRegion.nativeQ X).order :=
      (C9QPilotRegion.nativeQ X).order_pos
    exact one_lt_pow₀ hbase horder.ne'
  have hR : (1 : Real) < (fPlaceVolumeIndex X : Real) := by
    rw [h]
    exact hpow_gt_one
  exact_mod_cast hR

/-- In particular the signed criterion is false at volume index 1 (the already
known partial no-go), now recovered from the arithmetic form. -/
theorem signedCriterion_false_of_index_one
    (X : N8NativeInput l)
    (h : fPlaceVolumeIndex X = 1) :
    ¬ EtaFPlaceSignedComparisonTarget X := by
  intro htarget
  have hgt := signedCriterion_implies_index_gt_one X htarget
  omega

end LeanFormal.IUT.N8Closure.EtaSignedCriterionDisproof
