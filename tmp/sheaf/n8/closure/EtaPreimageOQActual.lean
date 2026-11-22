import tmp.sheaf.n8.closure.EtaContinuousAddEquivRecordActual2
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import Mathlib

/-!
# Preimage of O_Q and actual pushed normalization

Uses the actual norm bridge between the commonPrimeCompletion norm and the
normalizedCompletion norm, together with normalizedCompletion_norm_le_one_iff,
to prove (qoContinuousAddEquiv)⁻¹'(O_Q)=O_K.  Then Measure.map and the actual
muK(O_K)=1 give pushed(O_Q)=1.  No arbitrary normalization.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaNormalizedHaarTransportActual
open LeanFormal.IUT.N8Closure.EtaNormalizedHaarTransportActual2
open LeanFormal.IUT.N8Closure.EtaContinuousAddEquivRecordActual2
open LeanFormal.IUT.LocalFieldIntegralUnits

namespace LeanFormal.IUT.N8Closure.EtaPreimageOQActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [MeasurableSpace (EtaRssAdmissibleCorrection.K X)] [BorelSpace (EtaRssAdmissibleCorrection.K X)]
variable [ProperSpace (EtaRssAdmissibleCorrection.K X)] [IsUltrametricDist (EtaRssAdmissibleCorrection.K X)]
variable [LocallyCompactSpace (EtaRssAdmissibleCorrection.K X)]
variable [NormedSpace ℚ_[FPlacePrime X] (EtaRssAdmissibleCorrection.K X)]
variable [FiniteDimensional ℚ_[FPlacePrime X] (EtaRssAdmissibleCorrection.K X)]
variable [Nontrivial (EtaRssAdmissibleCorrection.K X)]
variable [NormSMulClass ℚ_[FPlacePrime X] (EtaRssAdmissibleCorrection.K X)]
variable [MeasurableSpace (QCompletion X)] [BorelSpace (QCompletion X)]
variable [ProperSpace (QCompletion X)] [IsUltrametricDist (QCompletion X)]
variable [LocallyCompactSpace (QCompletion X)]

/-- The commonPrimeCompletion norm is the normalizedCompletion norm. -/
theorem norm_commonPrime_eq_normalized
    (x : EtaRssAdmissibleCorrection.K X) :
    @norm (EtaRssAdmissibleCorrection.K X)
      (inferInstance : Norm (EtaRssAdmissibleCorrection.K X)) x =
    @norm (NormalizedCompletion (nativeFPlaceOverBad X))
      (inferInstance : Norm (NormalizedCompletion (nativeFPlaceOverBad X))) x := rfl

/-- O_Q is the norm<=1 closed ball. -/
theorem O_Q_eq_closedBall :
    O_Q X = Metric.closedBall (0 : QCompletion X) 1 := by
  ext x
  change x ∈ (Integers (QCompletion X) : Set (QCompletion X)) ↔
    x ∈ Metric.closedBall (0 : QCompletion X) 1
  rw [SetLike.mem_coe, LocalFieldIntegralUnits.mem_integers_iff,
    Metric.mem_closedBall, dist_zero_right]

/-- Actual preimage theorem. -/
theorem preimage_O_Q : (qoContinuousAddEquiv X) ⁻¹' (O_Q X) = O_K X := by
  ext x
  change (qoContinuousAddEquiv X) x ∈ (Integers (QCompletion X) : Set (QCompletion X)) ↔
    x ∈ (Integers (EtaRssAdmissibleCorrection.K X) :
      Set (EtaRssAdmissibleCorrection.K X))
  simp only [SetLike.mem_coe]
  rw [LocalFieldIntegralUnits.mem_integers_iff (K := QCompletion X),
    LocalFieldIntegralUnits.mem_integers_iff
      (K := EtaRssAdmissibleCorrection.K X)]
  have he : (qoContinuousAddEquiv X) x =
      (normalizedCompletionRingEquiv (nativeFPlaceOverBad X)) x := by
    change (qoCompletionHomeomorph X) x =
      (normalizedCompletionRingEquiv (nativeFPlaceOverBad X)) x
    rw [homeomorph_apply_eq_ringEquiv]
    simp [qoCompletionRingEquiv]
    rfl
  rw [he, norm_commonPrime_eq_normalized]
  exact normalizedCompletion_norm_le_one_iff (nativeFPlaceOverBad X) x

/-- Pushed measure is normalized at O_Q, closing the target. -/
theorem pushed_O_Q : (pushed X) (O_Q X) = 1 := by
  change (Measure.map (⇑(qoContinuousAddEquiv X).toHomeomorph) (μK X)) (O_Q X) = 1
  rw [Measure.map_apply (qoContinuousAddEquiv X).continuous.measurable
    (by rw [O_Q_eq_closedBall X]; exact measurableSet_closedBall)]
  change (μK X) ((qoContinuousAddEquiv X) ⁻¹' (O_Q X)) = 1
  rw [preimage_O_Q]
  exact μK_O_K X

theorem PushedNormalizedAtOQ_closed : PushedNormalizedAtOQ X :=
  pushed_O_Q X

end LeanFormal.IUT.N8Closure.EtaPreimageOQActual
