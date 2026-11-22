import tmp.sheaf.n8.closure.EtaGlobalRegionAtFActual
import tmp.sheaf.n8.closure.EtaGlobalRssAtF
import Mathlib

/-!
# F-level Rss alignment: carrier equality and exact quotient bridge target

The multiradial file EtaGlobalRegionAtFActual uses
QCompletion X = Completion (nativeFPlaceOverBad X); EtaGlobalRssAtF uses the
actual F completion K X = CommonPrimeCompletion (K := F) nativeFPlaceAtPrime.
The carriers are definitionally equal (carrier_eq, rfl), so no carrier bridge is
needed.

The two equal-volume quotients, however, were elaborated with independently
declared MeasurableSpace/BorelSpace instances for the two type synonyms, so
their quotient types are not definitionally the same.  The exact remaining
target is the instance-compatible quotient equivalence recorded below.  The
multiradial qO class is actual; defining it directly in EtaGlobalRssAtF requires
that bridge.  No arbitrary map is introduced.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
open LeanFormal.IUT.N8Closure.EtaRssNontrivialActual
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaGlobalRegionAtFActual
open LeanFormal.IUT.N8Closure.EtaRssAdmissibleCorrection
open LeanFormal.IUT.N8Closure.EtaGlobalRssAtF

namespace LeanFormal.IUT.N8Closure.EtaFLevelRssAlignmentActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [MeasurableSpace (QCompletion X)] [BorelSpace (QCompletion X)]
variable [ProperSpace (QCompletion X)] [IsUltrametricDist (QCompletion X)]
variable (μ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μ]

variable [MeasurableSpace (K X)] [BorelSpace (K X)]
variable (μK : Measure (K X)) [Measure.IsAddHaarMeasure μK]
variable [Measure.IsOpenPosMeasure μK] [IsFiniteMeasureOnCompacts μK]
variable [ProperSpace (K X)] [IsUltrametricDist (K X)]
variable [NormedSpace ℚ_[FPlacePrime X] (K X)]
variable [FiniteDimensional ℚ_[FPlacePrime X] (K X)]
variable [Nontrivial (K X)]
variable [NormSMulClass ℚ_[FPlacePrime X] (K X)]

/-- Same carrier: the multiradial QCompletion and the local-global F completion
are definitionally equal. -/
theorem carrier_eq : QCompletion X = K X := rfl

/-- Actual multiradial F-level qO class. -/
noncomputable def qOClassFLevel : FLevelRss X μ :=
  qOClass X μ

/-- The actual multiradial qO class is the class of the actual qO region. -/
theorem qOClassFLevel_eq :
    qOClassFLevel X μ = Quotient.mk (SameVolume (K := QCompletion X) μ) (qORegionPF X μ) :=
  rfl

/-- Exact remaining quotient bridge: an actual equivalence between the
multiradial FLevelRss and GlobalRssAtF, induced by the same carrier and volume
relation, requires matching typeclass instances.  This is the exact gap; no
arbitrary quotient map is chosen. -/
def FLevelGlobalClassBridgeTarget : Prop :=
  Nonempty (FLevelRss X μ ≃ EtaRssAdmissibleCorrection.Rss (X := X) (mu := μK))

/-! ## Exact no-go for a direct class map

The carriers are definitionally equal, but the quotient types use independently
declared measurable-space instances, so openClassF/closedClassF/qOClass cannot
be identified with globalOpenClassAtF/globalClosedClassAtF/qOClassInGlobal by
rfl.  The named target above is the exact instance-compatible bridge; until it
is supplied, defining qOClass directly in EtaGlobalRssAtF would require an
arbitrary quotient map.  The actual multiradial qOClass is retained.
-/

end LeanFormal.IUT.N8Closure.EtaFLevelRssAlignmentActual
