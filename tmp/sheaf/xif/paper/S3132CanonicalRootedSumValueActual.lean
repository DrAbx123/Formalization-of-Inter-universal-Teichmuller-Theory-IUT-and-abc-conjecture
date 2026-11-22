import tmp.sheaf.xif.paper.S3131CanonicalRootedQCActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000

noncomputable section
open scoped BigOperators

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3132CanonicalRootedSumValueActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-!
# task-41(a): the canonical rooted H_C readout as a rooted V-form sum (rfl)

**Component, not a paper object.**  Owner: hull.  Consumer: the sharper Theta
target `MissingCanonicalRootedThetaReadout` and shehdd's gate/
`S3140ThetaNormalizationLegActual`.

The canonical object is the mainline `S3131CanonicalRootedHC T mu`
(`S3131CanonicalRootedQCActual:67-71`); each `rootThetaHullLog` summand is
**defined** as `arithmeticTupleNormalizedLogVolume` at the rooted hull
(`RootHullContainmentInequalityActual:118-120`), so the rooted V-form value is
definitional.  This module records the rfl theorem with raised heartbeat limits
(the plain statement's elaboration needs more than the default limit because of
the dependent tensor-block instance search).

Pages: IUT III, Proposition 3.9, (i), p. 115; Corollary 3.12, corpus:10324-10353.
-/

/-- The canonical rooted H_C readout is the rooted sum of the actual
degree-normalized V-form Theta-hull log-volumes, with the actual bad local
weights. -/
theorem S3131CanonicalRootedHC_eq_rootedSum :
    S3131CanonicalRootedHC (l := l) T mu =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
            (mu b) (rootHalfCoefficient (l := l) T b) :=
  rfl

#check S3131CanonicalRootedHC_eq_rootedSum

end LeanFormal.IUT.XiFPaper.S3132CanonicalRootedSumValueActual

end
