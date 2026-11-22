import tmp.sheaf.xif.paper.S3132ConcreteSourceVFormInstantiatedActual

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
open LeanFormal.IUT.XiFPaper.S3136ConcreteExample36NativeDataActual
open LeanFormal.IUT.XiFPaper.S3132ConcreteSourceVFormInstantiatedActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideCanonicalConditionalActual

/-! # Paper-route Theta side: conditional canonical readout theorem (data modulo)

The canonical Theta-side readout theorem on the concrete Example 3.6 source,
conditional exactly on the two recorded residuals: the concrete native data
(SourceInitialThetaTuple + clauses A--F) and the V-form/canonical identity with
the additive Haar family.  The normalization factor residual is already CLOSED
(S3132ConcreteSourceNormalizationClosureActual), so this is the final conditional
form of the paper-route Theta side.  Component, not a paper object. -/

variable {l : PrimeGeFive}
variable (M : LGPConcreteExample36NativeDataMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpConcreteExample36NativeData M)))]

/-- **Conditional canonical readout theorem modulo the data residual.** -/
theorem thetaSideCanonicalReadout_conditional
    (h : MissingConcreteExample36VFormCanonicalReadout (l := l) M) :
    Real.log sourceHullRealLogVolume =
      S3131CanonicalRootedHC (l := l)
        (lgpConcreteExample36NativeData M)
        (lgpNativeHaarFamily (lgpConcreteExample36NativeData M)) :=
  concreteExample36CanonicalReadout (l := l) M h

/-- **Conditional raw readout theorem modulo the data residual.** -/
theorem thetaSideRawLogVolume_conditional
    (h : MissingConcreteExample36VFormCanonicalReadout (l := l) M) :
    Real.log ((sourceHullHaar sourceQlHullImage).toReal) =
      S3131CanonicalRootedHC (l := l)
        (lgpConcreteExample36NativeData M)
        (lgpNativeHaarFamily (lgpConcreteExample36NativeData M)) :=
  concreteExample36RawLogVolume_eq_canonical (l := l) M h

#check thetaSideCanonicalReadout_conditional
#check thetaSideRawLogVolume_conditional

end LeanFormal.IUT.XiFPaper.S3132ThetaSideCanonicalConditionalActual
end
