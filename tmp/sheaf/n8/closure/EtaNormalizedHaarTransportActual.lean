import tmp.sheaf.n8.closure.EtaNormalizedHaarBothActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeNormalizedCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import Mathlib

/-!
# Normalized Haar transport attempt at the actual F completion

The actual completion homeomorphism is
commonPrimeCompletionActualHomeomorph (nativeFPlaceAtPrime X) :
  K X ≃ₜ QCompletion X,
built from normalizedCompletionHomeomorph.  The underlying ring map is
normalizedCompletionRingEquiv, and normalizedCompletionIntegersEquiv identifies
the normalized integral unit ball with CompletionIntegers (not with the
canonical Integers ball of QCompletion).

This file records the actual homeomorph/ring equiv and the exact remaining
transport target.  The missing actual theorem is a continuous additive
equivalence preserving the canonical integral balls, not an arbitrary
homeomorphism; without it the normalized Haar measure cannot be transported
while preserving O-normalization.  No arbitrary transport is introduced.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.EtaNormalizedHaarBothActual

namespace LeanFormal.IUT.N8Closure.EtaNormalizedHaarTransportActual

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

/-- Actual homeomorphism from the F completion to the QCompletion carrier. -/
def qoCompletionHomeomorph :
    EtaRssAdmissibleCorrection.K X ≃ₜ QCompletion X :=
  commonPrimeCompletionActualHomeomorph (nativeFPlaceAtPrime X)

/-- Actual ring equivalence underlying the homeomorphism. -/
def qoCompletionRingEquiv :
    EtaRssAdmissibleCorrection.K X ≃+* QCompletion X :=
  normalizedCompletionRingEquiv (nativeFPlaceOverBad X)

/-- Actual normalized-integers equivalence. -/
def qoCompletionIntegersEquiv :
    Integers (EtaRssAdmissibleCorrection.K X) ≃+* CompletionIntegers (nativeFPlaceOverBad X) :=
  normalizedCompletionIntegersEquiv (nativeFPlaceOverBad X)

/-- Exact remaining transport target: normalized Haar measure on QCompletion
pushed to K along the actual completion homeomorphism and identified with the
normalized Haar measure on K. -/
def NormalizedHaarTransportTarget : Prop :=
  NormalizedHaarCarrierTransport (X := X)

/-! ## Exact no-go boundary

The actual homeomorphism qoCompletionHomeomorph is only topological; the
normalized ring equivalence is identity on underlying values, but there is no
production continuous additive equivalence preserving the canonical integral
balls: normalizedCompletionIntegersEquiv targets CompletionIntegers, while the
normalized Haar muQ is normalized at Integers (QCompletion).  The missing
actual theorem is that unit-ball identification (plus additive Haar transport
along it).  Hence the named target above is the exact gap; no arbitrary
homeomorphism or measure equality is used.
-/

end LeanFormal.IUT.N8Closure.EtaNormalizedHaarTransportActual
