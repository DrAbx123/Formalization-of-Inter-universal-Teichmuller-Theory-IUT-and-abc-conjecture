import tmp.sheaf.xif.paper.S3076OneColumnMagnitudeProducerActual
import tmp.sheaf.xif.paper.BaseQFamilyActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.S3076OneColumnMagnitudeProducerActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3076bSourceNativeQBridgeAttempt

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv} [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Expand the source one-column q as the actual source theater packet q. -/
theorem S3076b_oneColumnQ_expand :
    I.oneColumnQAtZero = (I.theaterAt 1 0).thetaPacket.q := rfl

/-- Expand the native local weight as the inverse actual completion degree. -/
theorem S3076b_nativeWeight_expand
    (b : Bad (nativePlaceSelection T)) :
    nativeBadLocalWeight T b =
      ((localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : Nat) : Real)⁻¹ :=
  nativeBadLocalWeight_eq_inv T b

/-- Expand the native base q log-magnitude as the negative log of the actual
completion norm. -/
theorem S3076b_baseQLog_expand
    (b : Bad (nativePlaceSelection T)) :
    baseQLogMagnitude T b =
      -Real.log ‖(nativeBaseQFamily T b).q‖ := rfl

/-- The exact first unproved source/native q equality: the one-column source q
absolute log equals the weighted sum of the native base q log-magnitudes,
written with the actual completion degrees and norms. -/
def S3076bExactMissingEq : Prop :=
  |Real.log ((I.theaterAt 1 0).thetaPacket.q)| =
    ∑ b : Bad (nativePlaceSelection T),
      ((localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : Nat) : Real)⁻¹ *
        (-Real.log ‖(nativeBaseQFamily T b).q‖)

/-- The expanded equality is exactly S3076WeightedLogBridge. -/
theorem S3076b_exactMissingEq_iff_weighted :
    S3076bExactMissingEq (I := I) T ↔
      S3076WeightedLogBridge (I := I) T := by
  unfold S3076bExactMissingEq S3076WeightedLogBridge
    S3076NativeWeightedLogSum
  rw [S3076b_oneColumnQ_expand]
  constructor <;> intro h
  · simpa only [S3076b_nativeWeight_expand, S3076b_baseQLog_expand] using h
  · simpa only [S3076b_nativeWeight_expand, S3076b_baseQLog_expand] using h

/-- Conditional producer of the weighted bridge from the expanded equality. -/
theorem S3076_weightedBridge_of_exactMissingEq
    (h : S3076bExactMissingEq (I := I) T) :
    S3076WeightedLogBridge (I := I) T :=
  (S3076b_exactMissingEq_iff_weighted (I := I) T).mp h

#check S3076b_oneColumnQ_expand
#check S3076b_nativeWeight_expand
#check S3076b_baseQLog_expand
#check S3076bExactMissingEq
#check S3076b_exactMissingEq_iff_weighted
#check S3076_weightedBridge_of_exactMissingEq
#print axioms S3076b_exactMissingEq_iff_weighted

end LeanFormal.IUT.XiFPaper.S3076bSourceNativeQBridgeAttempt
end
