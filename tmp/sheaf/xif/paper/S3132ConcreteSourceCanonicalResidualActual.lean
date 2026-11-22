import tmp.sheaf.xif.paper.S3132ConcreteSourceNormalizationClosureActual
import tmp.sheaf.xif.paper.S3131CanonicalRootedQCActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3132IQHullRealLogVolumeReadoutActual
open LeanFormal.IUT.XiFPaper.S3132ConcreteSourceNormalizationClosureActual

namespace LeanFormal.IUT.XiFPaper.S3132ConcreteSourceCanonicalResidualActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-!
# Theta-half remaining residual on the concrete source side: V-form = canonical rooted readout

**Component, not a paper object.**  Owner: hull.  Consumers: mainline
FINAL-STATUS/ledger; lattice index.

In `S3132ConcreteSourceNormalizationClosureActual` the label-level
normalization factor of the concrete Example 3.6 source model is PROVED to
vanish (`sourceThetaNormalizationFactor_eq_zero`, unit-reference Haar mass one),
so the sharper Theta target there reduces to the V-form/canonical identification

    sourceVFormLogVolume = S3131CanonicalRootedHC T mu,

the concrete-source analogue of `MissingVFormCanonicalIdentification`.  This
module states that identity as the minimal residual and composes it with the
closure:

* given the residual, the actual raw source reading equals the canonical rooted
  readout (`sourceRawLogVolume_eq_canonical_of_residual`) and the packaged
  source readout does too (`sourceCanonicalReadout_of_residual`).

**Why it is not yet discharged** (data missing, not missing mathematics):

1. there is no CONCRETE `SourceNativeInitialThetaData` in the tree for the
   Example 3.6 stage (`HodgeTheater` carries only arithmetic/prime-strip/theta
   packet; the concrete stage `concreteInitialThetaCStageTheater` has no native
   data field);
2. the canonical rooted readout needs a concrete Haar measure family `mu` on the
   native `qVFamTensorBlock` completions, which the tree does not construct;
3. the canonical readout is a weighted sum over the NATIVE BAD places of `F`
   (rooted tensor V-forms), while the concrete source model is the `Q_5`
   principal-unit log image; the paper identification of the two is exactly this
   rooted readout identity (Proposition 3.9, (i) normalization plus the rooted
   decomposition), so it remains exact data/identification.
Construction plan: instantiate `T` from the concrete stage/source theater native
data, construct `mu` as the normalized Haar on the actual completions (repo
tools: `commonPrimeCompletionActualRingEquiv`, `normalizedCompletionRingEquiv`),
then reduce to the rooted-hull/principal-unit identification.
Pages: IUT III, Proposition 3.9, (i), p. 115; Remark 3.9.5; Corollary 3.12
corpus:10324-10353; IUT IV, Proposition 1.4, (i).
-/

/-- **Minimal residual (concrete source side):** the label-level V-form of the
actual source hull image equals the canonical rooted `H_C` readout. -/
structure MissingConcreteVFormCanonicalReadout : Prop where
  vform_eq_canonical :
    sourceVFormLogVolume = S3131CanonicalRootedHC (l := l) T mu

/-- The residual in `Prop` (nonempty) form. -/
abbrev MissingConcreteVFormCanonicalReadoutProp : Prop :=
  Nonempty (MissingConcreteVFormCanonicalReadout (l := l) T mu)

/-- **Residual (1) gives the canonical raw source reading** (factor (2) already
closed). -/
theorem sourceRawLogVolume_eq_canonical_of_residual
    (h : MissingConcreteVFormCanonicalReadout (l := l) T mu) :
    Real.log ((sourceHullHaar sourceQlHullImage).toReal) =
      S3131CanonicalRootedHC (l := l) T mu :=
  sourceRawLogVolume_eq_canonical_of_VForm _ h.vform_eq_canonical

/-- **Residual (1) gives the packaged canonical source readout.** -/
theorem sourceCanonicalReadout_of_residual
    (h : MissingConcreteVFormCanonicalReadout (l := l) T mu) :
    Real.log sourceHullRealLogVolume = S3131CanonicalRootedHC (l := l) T mu :=
  sourceCanonicalReadout_of_VFormResidual _ h.vform_eq_canonical

#check MissingConcreteVFormCanonicalReadout
#check MissingConcreteVFormCanonicalReadoutProp
#check sourceRawLogVolume_eq_canonical_of_residual
#check sourceCanonicalReadout_of_residual

end LeanFormal.IUT.XiFPaper.S3132ConcreteSourceCanonicalResidualActual

end