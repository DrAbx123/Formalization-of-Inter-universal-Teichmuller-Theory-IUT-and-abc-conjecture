import tmp.sheaf.xif.paper.S3132ThetaSideModelClauseResidualActual

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
open LeanFormal.IUT.XiFPaper.S3132ThetaSideModelClauseResidualActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideSharpResidualActual

/-! # Paper-route Theta side: the single sharp residual record

Bundles the minimal exact data residual (stage4 `LGPModelSourceClauseMissing`:
concrete sign quotient + clause assembly A--F) with the one remaining identity
(source V-form = canonical rooted readout on the concrete Haar family).  This is
the sharpest single statement of what the paper-route Theta side still needs.
Component, not a paper object. -/

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- The sharp single residual: the V-form/canonical identity on the minimal
model data. -/
abbrev ThetaSideSharpResidual : Prop :=
  MissingConcreteVFormCanonicalReadout
    (T := lgpModelNativeData M)
    (lgpNativeHaarFamily (lgpModelNativeData M))

/-- The sharp residual is one real identity. -/
theorem thetaSideSharpResidual_iff :
    ThetaSideSharpResidual (l := l) M ↔
      (sourceVFormLogVolume =
        S3131CanonicalRootedHC (l := l)
          (lgpModelNativeData (l := l) M)
          (lgpNativeHaarFamily (lgpModelNativeData (l := l) M))) := by
  constructor
  · intro h; exact h.vform_eq_canonical
  · intro h; exact ⟨h⟩

/-- **The sharp residual alone yields the canonical packaged source readout**
(no further hypotheses; normalization is closed). -/
theorem thetaSideSharpResidual_canonicalReadout
    (h : ThetaSideSharpResidual (l := l) M) :
    Real.log sourceHullRealLogVolume =
      S3131CanonicalRootedHC (l := l)
        (lgpModelNativeData (l := l) M)
        (lgpNativeHaarFamily (lgpModelNativeData (l := l) M)) :=
  modelCanonicalReadout (l := l) M h

#check ThetaSideSharpResidual
#check thetaSideSharpResidual_iff
#check thetaSideSharpResidual_canonicalReadout

end LeanFormal.IUT.XiFPaper.S3132ThetaSideSharpResidualActual
end