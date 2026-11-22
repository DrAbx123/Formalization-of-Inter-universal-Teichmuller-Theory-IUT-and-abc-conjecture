import tmp.sheaf.xif.paper.S3136NativeHaarFamilyActual
import tmp.sheaf.xif.paper.S3132ConcreteSourceCanonicalResidualActual
import tmp.sheaf.xif.paper.S3131CanonicalRootedQCActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.S3132ConcreteSourceCanonicalResidualActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3132IQHullRealLogVolumeReadoutActual
open LeanFormal.IUT.XiFPaper.S3132ConcreteSourceNormalizationClosureActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideHaarIntegrationActual

/-! # Paper-route Theta side: concrete native Haar integration (stage4 consumer)

Uses stage4's S3136NativeHaarFamilyActual as the concrete mu for the canonical
rooted readout: lgpNativeHaarFamily T : (b) -> Measure (qVFamTensorBlock T b) is
the additive Haar family with IsAddHaarMeasure and the needed instance families.
Normalization is free (the (1/finrank)(log mu(S) - log mu(O)) readout is
invariant under mu |-> c*mu). Component, not a paper object; owner hull. -/

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The integrated concrete Haar family (definitional aliasing of stage4's). -/
noncomputable def thetaSideConcreteMu :
    (b : Bad (nativePlaceSelection T)) → Measure (qVFamTensorBlock T b) :=
  lgpNativeHaarFamily T

/-- Each member is additive Haar (integration check). -/
theorem thetaSideConcreteMu_isAddHaar (b : Bad (nativePlaceSelection T)) :
    Measure.IsAddHaarMeasure (thetaSideConcreteMu T b) := by
  unfold thetaSideConcreteMu
  infer_instance

/-- The canonical rooted readout with the concrete Haar family. -/
noncomputable def thetaSideCanonicalReadout : ℝ :=
  S3131CanonicalRootedHC (l := l) T (thetaSideConcreteMu T)

/-- The canonical readout with the concrete family is the canonical rooted
readout at the concrete Haar family (definitional). -/
theorem thetaSideCanonicalReadout_eq :
    thetaSideCanonicalReadout T =
      S3131CanonicalRootedHC (l := l) T (thetaSideConcreteMu T) :=
  rfl

/-- The residual with the concrete Haar family is exactly one real identity. -/
theorem thetaSideResidual_iff_identity :
    MissingConcreteVFormCanonicalReadout (T := T) (thetaSideConcreteMu T) ↔
      (sourceVFormLogVolume =
        S3131CanonicalRootedHC (l := l) T (thetaSideConcreteMu T)) := by
  constructor
  · intro h
    exact h.vform_eq_canonical
  · intro h
    exact ⟨h⟩

#check thetaSideConcreteMu
#check thetaSideConcreteMu_isAddHaar
#check thetaSideCanonicalReadout
#check thetaSideCanonicalReadout_eq
#check thetaSideResidual_iff_identity

end LeanFormal.IUT.XiFPaper.S3132ThetaSideHaarIntegrationActual
end