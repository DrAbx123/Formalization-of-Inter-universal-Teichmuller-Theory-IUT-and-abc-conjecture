import tmp.sheaf.xif.paper.S3131CanonicalRootedQCActual
import tmp.sheaf.xif.paper.S3134MainlineRootedHFaActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

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
open LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3132CanonicalVFormValueActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-!
# task-41(a) V-form value lemma for the canonical rooted H_C readout

**Component, not a paper object.**  Owner: hull.  Consumer: the sharper target
`MissingCanonicalRootedThetaReadout` (task-41) and the delivery note to shehdd.

Per shehdd's answer, the canonical object is the mainline
`S3131CanonicalRootedHC T mu` (namespace `S3131CanonicalRootedQCActual`;
definition at lines 67-71: the rooted sum of `rootThetaHullLog` terms with the
actual bad local weights), and each `rootThetaHullLog` summand is *defined* as
`arithmeticTupleNormalizedLogVolume` at the rooted hull
(`RootHullContainmentInequalityActual:118-120`).  Hence the V-form value of the
canonical readout is **definitional** (recorded as such; no separate bridge
theorem is needed):

    S3131CanonicalRootedHC T mu
      = ∑ b, nativeBadLocalWeight T b *
          rootThetaHullLog (qVFamTensorPlaces T b) qVFamTensorTuple
            (mu b) (rootHalfCoefficient T b),
    rootThetaHullLog ... = arithmeticTupleNormalizedLogVolume ... (rooted hull).

The alias theorem below records that shehdd's `S3134CanonicalRootedHC` is
definitionally the mainline readout, so the sharper target
`thetaPilotHullLogVolumeReal C3 = S3134CanonicalRootedHC T mu` can be stated
against `S3131CanonicalRootedHC T mu` with no convention bridge.
Pages: IUT III, Proposition 3.9, (i), p. 115; Corollary 3.12, corpus:10324-10353.
-/

/-- shehdd's alias `S3134CanonicalRootedHC` is definitionally the mainline
canonical rooted V-form readout. -/
theorem S3134CanonicalRootedHC_eq_S3131CanonicalRootedHC :
    S3134CanonicalRootedHC T mu = S3131CanonicalRootedHC T mu :=
  rfl

#check S3134CanonicalRootedHC_eq_S3131CanonicalRootedHC

end LeanFormal.IUT.XiFPaper.S3132CanonicalVFormValueActual

end
