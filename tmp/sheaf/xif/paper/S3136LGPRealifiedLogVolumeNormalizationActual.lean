import tmp.sheaf.xif.paper.S3136LGPBadWeightNormalizationActual

/-! # Stage-4 host: normalized realified log-value identities

Source anchors: IUT III, Remark 3.9.4; Prop. 3.9, (i), p. 115; IUT II,
Remark 2.5.1, (i).

This file relates the actual bad weights to the actual normalized bad weights
and to the realified log values:
* lgpBadWeight_eq_normalized_mul_sum: weight = normalized weight * total;
* lgpBadRealifiedLogValue_eq_normalized: the realified log value is ofAdd of
  normalized weight times the total;
* lgpBadWeightSum_pos / sum-one restatements for consumers.

LABEL: prerequisite component only.  Consumer: lattice R1/R-C, abc F4. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPRealifiedLogVolumeNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.S3136LGPWeightAgreementBridgeActual
open LeanFormal.IUT.XiFPaper.S3136LGPBadWeightNormalizationActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- The actual bad weight is the normalized weight times the actual total. -/
theorem lgpBadWeight_eq_normalized_mul_sum
    (b : Bad (nativePlaceSelection T)) :
    lgpBadWeight T b = lgpBadNormalizedWeight T b * lgpBadWeightSum T := by
  unfold lgpBadNormalizedWeight
  exact (div_mul_cancel₀ (lgpBadWeight T b)
    (ne_of_gt (lgpBadWeightSum_pos T))).symm

/-- The realified log value in terms of the normalized weight and the total. -/
theorem lgpBadRealifiedLogValue_eq_normalized
    (b : Bad (nativePlaceSelection T)) :
    lgpBadRealifiedLogValue T b =
      Multiplicative.ofAdd (lgpBadNormalizedWeight T b * lgpBadWeightSum T) := by
  unfold lgpBadRealifiedLogValue
  rw [lgpBadWeight_eq_normalized_mul_sum]

/-- The normalized weights sum to one (restated for consumers). -/
theorem lgpBadNormalizedWeight_total' :
    (∑ b : Bad (nativePlaceSelection T), lgpBadNormalizedWeight T b) = 1 :=
  lgpBadNormalizedWeight_total T

#check lgpBadWeight_eq_normalized_mul_sum
#check lgpBadRealifiedLogValue_eq_normalized
#check lgpBadNormalizedWeight_total'

end LeanFormal.IUT.XiFPaper.S3136LGPRealifiedLogVolumeNormalizationActual
end