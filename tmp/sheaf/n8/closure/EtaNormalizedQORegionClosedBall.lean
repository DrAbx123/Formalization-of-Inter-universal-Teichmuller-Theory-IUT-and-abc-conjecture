import tmp.sheaf.n8.closure.EtaNormalizedQCompletionAlias
import tmp.sheaf.n8.closure.EtaNormalizedAliasCarrierActual
import tmp.sheaf.n8.closure.EtaFPlaceNormAgreementActualAttempt
import tmp.sheaf.n8.closure.EtaKfClosedBallEqQORegion
import Mathlib

/-!
# Normalized qO region closed ball

On the production NormalizedCompletion alias, the qO region q * Integers is the
closed ball of radius ||native q|| (normalized norm), by the same nonarchimedean
Integers argument as the Kf identity.  Under the native norm power relation,
this closed ball equals the corrected Kf carrier, closing the alias carrier gap
and hence canonicalNormalizedQOReadout = correctedGlobalQOReadout.  No arbitrary
cast is used.
-/

noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaGlobalRegionAtFActual
open LeanFormal.IUT.N8Closure.EtaGlobalQOReadoutDegreeActual
open LeanFormal.IUT.N8Closure.EtaGlobalQODegreeCorrectedAlignment
open LeanFormal.IUT.N8Closure.EtaKfClosedBallEqQORegion
open LeanFormal.IUT.N8Closure.EtaNormalizedQCompletionAlias
open LeanFormal.IUT.N8Closure.EtaNormalizedAliasCarrierActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormAgreementActualAttempt
open LeanFormal.IUT.N8Closure.EtaQOAddHaarNormalizedCalibrationActual
open LeanFormal.IUT.N8Closure.EtaQORegionMassNormFromScaling
open LeanFormal.IUT.N8Closure.EtaRssAdmissibleCorrection
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection

namespace LeanFormal.IUT.N8Closure.EtaNormalizedQORegionClosedBall

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [MeasurableSpace (QCompletion X)] [BorelSpace (QCompletion X)]
variable [ProperSpace (QCompletion X)] [IsUltrametricDist (QCompletion X)]
variable [LocallyCompactSpace (QCompletion X)]

local instance hKmeas : MeasurableSpace (K X) :=
  EtaPStepNormLink.nativePMeasurableSpace X

local instance hKborel : BorelSpace (K X) :=
  EtaPStepNormLink.nativePBorelSpace X

/-- The normalized qO region is the closed ball of radius ||native q||. -/
theorem normalizedQORegion_eq_closedBall :
    normalizedQORegion X =
      Metric.closedBall (0 : NormalizedQCompletion X) ‖nativeQNormalized X‖ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_mul]
    have hy : ‖(y : NormalizedQCompletion X)‖ ≤ 1 :=
      (mem_integers_iff (K := NormalizedQCompletion X) _).mp y.2
    calc
      ‖nativeQNormalized X‖ * ‖(y : NormalizedQCompletion X)‖
          ≤ ‖nativeQNormalized X‖ * 1 :=
        mul_le_mul_of_nonneg_left hy (norm_nonneg _)
      _ = ‖nativeQNormalized X‖ := mul_one _
  · intro hx
    have hq : nativeQNormalized X ≠ 0 := by
      intro h
      exact (C9QPilotRegion.nativeQ X).q_ne_zero
        (show ((C9QPilotRegion.nativeQ X).q : Completion (nativeFPlaceOverBad X)) = 0 from h)
    refine ⟨⟨x / nativeQNormalized X, ?_⟩, ?_⟩
    · rw [mem_integers_iff (K := NormalizedQCompletion X)]
      have hxle : ‖x‖ ≤ ‖nativeQNormalized X‖ := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      rw [norm_div, div_le_one (norm_pos_iff.mpr hq)]
      exact hxle
    · field_simp [hq]

/-- Under the norm power relation, the normalized closed ball equals the
corrected Kf carrier. -/
theorem normalizedQORegion_eq_correctedGlobalQOCarrier
    (hpow : NativeNormPowerRelation X)
    (hrel : (relDegree X : ℝ) ≠ 0) :
    normalizedQORegion X = correctedGlobalQOCarrier X := by
  rw [normalizedQORegion_eq_closedBall, correctedGlobalQOCarrier]
  congr 1
  have hnorm : ‖nativeQNormalized X‖ = ‖normalizedQVal X‖ := rfl
  rw [hnorm, hpow]
  exact (Real.pow_rpow_inv_natCast (norm_nonneg _) (Nat.cast_ne_zero.mp hrel)).symm

/-- Alias carrier gap closed. -/
theorem normalizedAliasCarrierGap_closed
    (hpow : NativeNormPowerRelation X)
    (hrel : (relDegree X : ℝ) ≠ 0) :
    NormalizedAliasCarrierGap X :=
  normalizedQORegion_eq_correctedGlobalQOCarrier (X := X) hpow hrel

/-- Readout equality closing the alias route. -/
theorem canonicalNormalizedQOReadout_eq_correctedGlobalQOReadout
    (hpow : NativeNormPowerRelation X)
    (hrel : (relDegree X : ℝ) ≠ 0) :
    canonicalNormalizedQOReadout X = correctedGlobalQOReadout X :=
  normalizedAliasCarrier_eq_corrected (X := X)
    (normalizedAliasCarrierGap_closed (X := X) hpow hrel)

end LeanFormal.IUT.N8Closure.EtaNormalizedQORegionClosedBall
