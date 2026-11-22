import tmp.sheaf.xif.paper.S3076bSourceNativeQBridgeAttempt
import tmp.sheaf.xif.paper.BaseQFamilyActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual

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
open LeanFormal.IUT.XiFPaper.S3076bSourceNativeQBridgeAttempt
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3076cWeightedProductAttempt

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv} [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Norm-level product bridge: the source one-column q is the weighted
product of the norms of the native base q family. -/
def S3076cNormProductBridge : Prop :=
  I.oneColumnQAtZero =
    ∏ b : Bad (nativePlaceSelection T),
      Real.exp (nativeBadLocalWeight T b *
        Real.log ‖(nativeBaseQFamily T b).q‖)

/-- If the norm product bridge holds and the resulting product is < 1, then
the weighted log bridge (S3076WeightedLogBridge) follows by log rules. -/
theorem S3076c_weightedBridge_of_normProduct
    (hprod : S3076cNormProductBridge (I := I) T)
    (hsign : Real.log (∏ b : Bad (nativePlaceSelection T),
      Real.exp (nativeBadLocalWeight T b *
        Real.log ‖(nativeBaseQFamily T b).q‖)) < 0) :
    S3076WeightedLogBridge (I := I) T := by
  unfold S3076cNormProductBridge at hprod
  unfold S3076WeightedLogBridge S3076NativeWeightedLogSum
  rw [hprod]
  have hlog :
      Real.log (∏ b : Bad (nativePlaceSelection T),
        Real.exp (nativeBadLocalWeight T b *
          Real.log ‖(nativeBaseQFamily T b).q‖)) =
        ∑ b : Bad (nativePlaceSelection T),
          nativeBadLocalWeight T b *
            Real.log ‖(nativeBaseQFamily T b).q‖ := by
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl ?_
      intro b hb
      rw [Real.log_exp]
    · intro b hb
      exact (Real.exp_pos _).ne'
  rw [abs_of_neg hsign, hlog]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro b hb
  rw [S3076b_baseQLog_expand]
  ring

#check S3076cNormProductBridge
#check S3076c_weightedBridge_of_normProduct
#print axioms S3076c_weightedBridge_of_normProduct

end LeanFormal.IUT.XiFPaper.S3076cWeightedProductAttempt
end
