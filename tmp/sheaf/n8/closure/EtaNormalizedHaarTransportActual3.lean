import tmp.sheaf.n8.closure.EtaNormalizedHaarTransportActual2
import Mathlib

/-!
# Normalized Haar transport 3: attempt and exact no-go

The actual objects are qoCompletionRingEquiv : K ≃+* QCompletion and
qoCompletionHomeomorph : K ≃ₜ QCompletion, plus the actual set equality
O_Q_set_eq between Integers(QCompletion) and CompletionIntegers.

The pushforward construction requires:
1. a continuous additive equivalence with compatible measurable structures
   (the homeomorph is topological; the ring equivalence is identity on
   underlying values but no continuous-additive instance is recorded);
2. AddEquiv.isAddHaarMeasure_map for the pushed measure;
3. Haar uniqueness for the normalized pair at the integral ball.

The exact target is recorded below; no arbitrary transport/measure equality.
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

namespace LeanFormal.IUT.N8Closure.EtaNormalizedHaarTransportActual3

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

/-- Actual additive equivalence below the completion ring equivalence. -/
def qoAddEquiv : EtaRssAdmissibleCorrection.K X ≃+ QCompletion X :=
  (qoCompletionRingEquiv X).toAddEquiv

/-- Exact target: the pushforward of the normalized K-Haar measure equals the
normalized QCompletion-Haar measure. -/
def PushedHaarEqualsMuQTarget : Prop :=
  EtaNormalizedHaarBothActual.NormalizedHaarCarrierTransport (X := X)

/-! ## Exact no-go boundary

No continuous additive equivalence with compatible measurable structures is
recorded (qoCompletionHomeomorph is only topological; qoAddEquiv's continuity
is not a production instance).  Consequently AddEquiv.isAddHaarMeasure_map and
the normalized-Haar uniqueness step cannot be instantiated.  The missing
theorems are: continuity of qoAddEquiv (both directions) and Haar uniqueness
for the normalized pair at O, after the actual O_Q_set_eq set comparison.
-/

end LeanFormal.IUT.N8Closure.EtaNormalizedHaarTransportActual3
