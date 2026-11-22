import tmp.sheaf.n8.closure.EtaNormalizedHaarTransportActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import Mathlib

/-!
# Normalized Haar transport 2: Integers/CompletionIntegers comparison

Integers (QCompletion X) is a Subring; production CompletionIntegers place is
a ValuationSubring, so the two types are not defeq by rfl.  Their underlying
carrier sets are nevertheless equal: both are the norm <= 1 ball of the same
completion.  This file proves that actual set equality and records the exact
remaining Haar transport target (continuous additive equivalence preserving
the integral balls plus Measure.map Haar).
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
open LeanFormal.IUT.N8Closure.EtaNormalizedHaarBothActual
open LeanFormal.IUT.N8Closure.EtaNormalizedHaarTransportActual
open LeanFormal.IUT.LocalFieldIntegralUnits

namespace LeanFormal.IUT.N8Closure.EtaNormalizedHaarTransportActual2

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

/-- The canonical Integers ball of QCompletion and the production
CompletionIntegers ball have the same underlying set (norm <= 1). -/
theorem O_Q_set_eq :
    (Integers (QCompletion X) : Set (QCompletion X)) =
      (CompletionIntegers (nativeFPlaceOverBad X) : Set (QCompletion X)) := by
  ext x
  change x ∈ (Integers (QCompletion X) : Set (QCompletion X)) ↔
    x ∈ (CompletionIntegers (nativeFPlaceOverBad X) : Set (QCompletion X))
  simp only [SetLike.mem_coe]
  rw [LocalFieldIntegralUnits.mem_integers_iff (K := QCompletion X) x,
    mem_completionIntegers_iff_norm_le_one (nativeFPlaceOverBad X) x]

/-- Exact remaining target: actual Haar measure equality after transporting muQ
to K along a continuous additive equivalence preserving O. -/
def NormalizedHaarTransportTarget2 : Prop :=
  NormalizedHaarCarrierTransport (X := X)

/-! ## Exact no-go boundary

The types Integers (QCompletion X) (Subring) and CompletionIntegers place
(ValuationSubring) are not rfl/defeq; their sets are equal by O_Q_set_eq, but
turning that into a normalized measure transport needs the missing actual
continuous additive equivalence preserving the integral balls, together with
the corresponding Measure.map Haar invariant theorem.  The named target above
is that exact gap; no arbitrary measure or homeomorphism is used.
-/

end LeanFormal.IUT.N8Closure.EtaNormalizedHaarTransportActual2
