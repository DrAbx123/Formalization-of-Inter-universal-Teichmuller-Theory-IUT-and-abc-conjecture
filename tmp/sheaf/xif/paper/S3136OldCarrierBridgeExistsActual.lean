import tmp.sheaf.xif.paper.S2586IQHullLogVolumeInstantiationActual

/-! # Stage-4 host: mining the old attempts — the concrete carrier bridge EXISTS

PRIOR ART (§7.9, checked first): tmp/sheaf/xif/paper/S2586IQHullLogVolumeInstantiationActual.lean:32
defines S2586IQHullLogVolumeInterface T b : IQHullLogVolumeInterface (qVFamTensorBlock T b)
with imageSet := rootThetaImageSet, hull := rootNormHull, logVolume := Measure.addHaar,
unitRegion := arithmeticTupleCanonicalUnitReference, scaleShift := id, and the two
finiteness/monotonicity fields proved.  This IS the measure-to-IQ carrier bridge whose
absence was recorded earlier in S3136CarrierBridgeAttemptActual; the old attempt
already instantiates the interface, so no new bridge construction is needed.

HONESTY NOTE: the carrier has Haar measure with null singletons, so POINTS have
log-volume 0 (S2590PadicSingletonNullActual).  The interface is therefore a genuine
measure carrier but its point log-volumes are DEGENERATE relative to the paper's
point-height comparison; this file exposes the interface and the degeneracy note, no
estimate is claimed.

LABEL: reuse adapter (old-attempt prior art). Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136OldCarrierBridgeExistsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open MeasureTheory

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

/-- The concrete IQ interface over the native Haar carrier (old-attempt reuse). -/
def lgpNativeIQInterface : IQHullLogVolumeInterface (qVFamTensorBlock T b) :=
  S2586IQHullLogVolumeInterface (l := l) T b

/-- Its log-volume is the native additive Haar measure (definitional). -/
theorem lgpNativeIQInterface_logVolume (S : Set (qVFamTensorBlock T b)) :
    (lgpNativeIQInterface T b).logVolume S =
      (Measure.addHaar : Measure (qVFamTensorBlock T b)) S := rfl

/-- Its scale shift is the identity (definitional). -/
theorem lgpNativeIQInterface_scaleShift :
    (lgpNativeIQInterface T b).scaleShift = id := rfl

/-- The concrete interface exists. -/
theorem lgpNativeIQInterface_exists :
    Nonempty (IQHullLogVolumeInterface (qVFamTensorBlock T b)) :=
  ⟨lgpNativeIQInterface T b⟩

#check lgpNativeIQInterface
#check lgpNativeIQInterface_logVolume
#check lgpNativeIQInterface_scaleShift
#check lgpNativeIQInterface_exists

end LeanFormal.IUT.XiFPaper.S3136OldCarrierBridgeExistsActual
end