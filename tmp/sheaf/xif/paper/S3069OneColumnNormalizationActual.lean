import tmp.sheaf.xif.paper.S1675GlobalReadoutNormalizationActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.ThetaLinkLogKummerActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S1675GlobalReadoutNormalizationActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3069OneColumnNormalizationActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv} [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The magnitude form of the one-column normalization: the absolute one-column
q log equals the native normalized q magnitude. -/
def S3069OneColumnMagnitudeEq : Prop :=
  |Real.log I.oneColumnQAtZero| =
    nativeGlobalQPilotNormalizedLogMagnitude (T := T)

/-- S1675OneColumnNormalization is exactly the magnitude equality. -/
theorem S3069OneColumnNormalization_iff :
    S1675OneColumnNormalization (I := I) T ↔
      S3069OneColumnMagnitudeEq (I := I) T := by
  unfold S1675OneColumnNormalization S3069OneColumnMagnitudeEq
  unfold qPilotSignedLogVolume nativeGlobalQPilotNormalizedSignedLogVolume
  constructor <;> intro h
  · exact neg_inj.mp h
  · rw [h]

/-- Actual reduction: the one-column normalization is equivalent to the
absolute one-column q log being the native normalized q magnitude. -/
theorem S3069_normalization_of_magnitude
    (h : S3069OneColumnMagnitudeEq (I := I) T) :
    S1675OneColumnNormalization (I := I) T :=
  (S3069OneColumnNormalization_iff (I := I) T).mpr h

#check S3069OneColumnMagnitudeEq
#check S3069OneColumnNormalization_iff
#check S3069_normalization_of_magnitude
#print axioms S3069OneColumnNormalization_iff

end LeanFormal.IUT.XiFPaper.S3069OneColumnNormalizationActual
end
