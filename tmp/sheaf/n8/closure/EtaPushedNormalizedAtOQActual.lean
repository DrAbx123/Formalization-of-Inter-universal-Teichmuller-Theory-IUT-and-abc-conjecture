import tmp.sheaf.n8.closure.EtaContinuousAddEquivRecordActual2
import Mathlib

/-!
# Pushed Haar normalization at O_Q: exact no-go

The actual ContinuousAddEquiv record and pushed Haar are available.  Closing
pushed(O_Q)=1 requires the actual preimage comparison
qoContinuousAddEquiv^{-1}(O_Q)=O_K.  The set-level comparison O_Q_set_eq is
available, but the norm-instance bridge between the commonPrimeCompletion norm
and the normalizedCompletion norm (used by
normalizedCompletion_norm_le_one_iff) does not elaborate directly, so the
preimage/measure-map theorem is the exact remaining gap.  No arbitrary
normalization is introduced.
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

namespace LeanFormal.IUT.N8Closure.EtaPushedNormalizedAtOQActual

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

/-- Exact preimage target needed for pushed(O_Q)=1. -/
def PreimageOQEqualsOK : Prop :=
  (qoContinuousAddEquiv X) ⁻¹' (O_Q X) = O_K X

/-! ## Exact no-go boundary

The missing actual theorem is the preimage comparison
qoContinuousAddEquiv^{-1}(O_Q)=O_K, which requires a norm-instance bridge
between commonPrimeCompletion (normalized completion norm) and the
NormalizedCompletion norm used by normalizedCompletion_norm_le_one_iff.  The
set equality O_Q_set_eq alone is insufficient for the Measure.map computation.
No arbitrary normalization or transport is used.
-/

end LeanFormal.IUT.N8Closure.EtaPushedNormalizedAtOQActual
