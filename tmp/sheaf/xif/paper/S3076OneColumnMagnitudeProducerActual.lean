import tmp.sheaf.xif.paper.S3069OneColumnNormalizationActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S3069OneColumnNormalizationActual
open LeanFormal.IUT.XiFPaper.S1675GlobalReadoutNormalizationActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3076OneColumnMagnitudeProducerActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv} [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The exact weighted native sum for S3069's magnitude. -/
noncomputable def S3076NativeWeightedLogSum : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * baseQLogMagnitude T b

/-- The exact first unproved equality: the one-column q absolute log equals
the weighted native base-q log sum. -/
def S3076WeightedLogBridge : Prop :=
  |Real.log I.oneColumnQAtZero| = S3076NativeWeightedLogSum (T := T)

/-- S3069's magnitude equality is exactly the weighted native sum equality. -/
theorem S3076_bridge_iff_magnitude :
    S3076WeightedLogBridge (I := I) T ↔
      S3069OneColumnMagnitudeEq (I := I) T := by
  unfold S3076WeightedLogBridge S3076NativeWeightedLogSum
  unfold S3069OneColumnMagnitudeEq
  rw [nativeGlobalQPilotNormalizedLogMagnitude_eq]

/-- Conditional producer of S3069 from the weighted bridge. -/
theorem S3076_magnitude_eq_of_bridge
    (h : S3076WeightedLogBridge (I := I) T) :
    S3069OneColumnMagnitudeEq (I := I) T :=
  (S3076_bridge_iff_magnitude (I := I) T).mp h

/-- Conditional producer of S1675OneColumnNormalization from the bridge. -/
theorem S3076_oneColumnNormalization_of_bridge
    (h : S3076WeightedLogBridge (I := I) T) :
    S1675OneColumnNormalization (I := I) T :=
  S3069_normalization_of_magnitude (I := I) T
    (S3076_magnitude_eq_of_bridge (I := I) T h)

theorem S3076_oneColumnQ_eq_packet_q :
    I.oneColumnQAtZero = (I.oneColumnPacket 0).q := rfl

#check S3076NativeWeightedLogSum
#check S3076WeightedLogBridge
#check S3076_bridge_iff_magnitude
#check S3076_oneColumnNormalization_of_bridge
#check S3076_oneColumnQ_eq_packet_q
#print axioms S3076_bridge_iff_magnitude

end LeanFormal.IUT.XiFPaper.S3076OneColumnMagnitudeProducerActual
end
