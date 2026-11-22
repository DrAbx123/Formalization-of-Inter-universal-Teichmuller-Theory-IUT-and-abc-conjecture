import tmp.sheaf.xif.paper.S3136ModelNativeDataWithHaarActual
import tmp.sheaf.xif.paper.S3132ConcreteSourceCanonicalResidualActual
import tmp.sheaf.xif.paper.S3131CanonicalRootedQCActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

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
open LeanFormal.IUT.XiFPaper.S3132ConcreteSourceCanonicalResidualActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelClauseWitnessAdapterActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideModelClauseResidualActual

/-! # Paper-route Theta side: residual on stage4's MINIMAL model clause data

Consumes stage4's `LGPModelSourceClauseMissing` — the minimal missing field-level
data (a concrete sign quotient over the concrete Gaussian arithmetic plus the
clause assembly A--F) — via `lgpModelNativeData` and
`lgpModelNativeDataWithHaar`.  This is the sharpest data-residual form of the
paper-route Theta side.  Component, not a paper object. -/

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- The model native datum from the minimal clause data. -/
abbrev modelNativeData : SourceNativeInitialThetaData.{0} l :=
  lgpModelNativeData M

/-- The bundled datum + concrete additive Haar family (stage4). -/
def modelNativeDataWithHaar : LGPModelNativeDataWithHaar l :=
  lgpModelNativeDataWithHaar M

/-- **The minimal-data Theta-side residual:** source V-form = canonical rooted
readout on the model datum with the concrete Haar family. -/
abbrev ModelSideVFormResidual : Prop :=
  MissingConcreteVFormCanonicalReadout
    (T := modelNativeData (l := l) M)
    (lgpNativeHaarFamily (modelNativeData (l := l) M))

/-- **Canonical packaged source readout from the minimal-data residual.** -/
theorem modelCanonicalReadout
    (h : ModelSideVFormResidual (l := l) M) :
    Real.log sourceHullRealLogVolume =
      S3131CanonicalRootedHC (l := l)
        (modelNativeData (l := l) M)
        (lgpNativeHaarFamily (modelNativeData (l := l) M)) :=
  sourceCanonicalReadout_of_residual
    (T := modelNativeData (l := l) M)
    (mu := lgpNativeHaarFamily (modelNativeData (l := l) M)) h

/-- **Canonical raw source reading from the minimal-data residual.** -/
theorem modelRawLogVolume_eq_canonical
    (h : ModelSideVFormResidual (l := l) M) :
    Real.log ((sourceHullHaar sourceQlHullImage).toReal) =
      S3131CanonicalRootedHC (l := l)
        (modelNativeData (l := l) M)
        (lgpNativeHaarFamily (modelNativeData (l := l) M)) :=
  sourceRawLogVolume_eq_canonical_of_residual
    (T := modelNativeData (l := l) M)
    (mu := lgpNativeHaarFamily (modelNativeData (l := l) M)) h

#check ModelSideVFormResidual
#check modelNativeDataWithHaar
#check modelCanonicalReadout
#check modelRawLogVolume_eq_canonical

end LeanFormal.IUT.XiFPaper.S3132ThetaSideModelClauseResidualActual
end
