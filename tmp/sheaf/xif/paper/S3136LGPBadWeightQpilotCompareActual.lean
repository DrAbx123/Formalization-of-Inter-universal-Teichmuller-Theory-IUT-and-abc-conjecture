import tmp.sheaf.xif.paper.S3136LGPBadWeightNormalizationActual
import tmp.sheaf.xif.paper.S3133S3131WeightNormalizationActual

/-! # Stage-4 host: comparison of the actual LGP bad weights with the qpilot weights

Source anchors: IUT III, Remark 3.1.1, (ii)-(iv), pp. 95--97 (weights
1/N_v, N_v a product of completion degrees, plus a positive normalization
factor); IUT II, Remark 2.5.1, (i); IUT III, Remark 3.9.4.

This file compares the actual LGP bad weights (q_v divisor exponents) with the
actual qpilot Remark 3.1.1 weights (inverse completion-degree weights):
* lgpQpilotWeightSum: the qpilot actual raw weight total;
* lgpQpilotBothNormalized_total: both actual normalized families sum to one
  (our lgpBadNormalizedWeight_total and qpilot S3131NormalizedWeightTotal);
* lgpBadNormalizedWeight_eq_qpilot_of_weightAgreement: CONDITIONAL comparison:
  if the two raw weight families agree pointwise, then the normalized families
  agree pointwise;
* LGPBadWeightQpilotComparisonMissing/Gap: exact missing data (pointwise weight
  family agreement, normalization factor relation, log-volume reading
  relation; refs above).

LABEL: prerequisite component only.  Consumer: lattice R1/R-C, mainline M4,
abc F4 (a). -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPBadWeightQpilotCompareActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.W6ActualPilotMonodromyActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3133QPilotLogVolumeSignActual
open LeanFormal.IUT.XiFPaper.S3133S3131WeightNormalizationActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.S3136LGPWeightAgreementBridgeActual
open LeanFormal.IUT.XiFPaper.S3136LGPBadWeightNormalizationActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]

/-- The qpilot actual raw weight total (Remark 3.1.1 weights). -/
noncomputable def lgpQpilotWeightSum : ℝ := S3131WeightSum T

/-- Both actual normalized families sum to one. -/
theorem lgpQpilotBothNormalized_total
    [Nonempty (Bad (nativePlaceSelection T))] :
    (∑ b : Bad (nativePlaceSelection T), lgpBadNormalizedWeight T b) = 1 ∧
      (∑ b : Bad (nativePlaceSelection T), S3131NormalizedWeight T b) = 1 :=
  ⟨lgpBadNormalizedWeight_total T, S3131NormalizedWeightTotal T⟩

/-- Conditional comparison: pointwise agreement of the raw weight families
implies agreement of the normalized families. -/
theorem lgpBadNormalizedWeight_eq_qpilot_of_weightAgreement
    (h : ∀ b : Bad (nativePlaceSelection T),
      lgpBadWeight T b = nativeBadLocalWeight T b)
    (b : Bad (nativePlaceSelection T)) :
    lgpBadNormalizedWeight T b = S3131NormalizedWeight T b := by
  have hsum : lgpBadWeightSum T = S3131WeightSum T := by
    unfold lgpBadWeightSum S3131WeightSum
    exact Finset.sum_congr rfl (fun b _ => h b)
  unfold lgpBadNormalizedWeight S3131NormalizedWeight
  rw [hsum, h b]

/-- Exact missing data for the comparison with the qpilot Remark 3.1.1 weights
(IUT III, Remark 3.1.1, (ii)-(iv), pp. 95--97; IUT II, Remark 2.5.1, (i);
IUT III, Remark 3.9.4):
* weightFamilyAgreement: pointwise agreement of the q_v divisor-exponent
  weights with the inverse completion-degree weights;
* normalizationFactor: the relation between the two positive normalization
  factors;
* logVolumeReading: the relation of the two normalized log-volume readings. -/
structure LGPBadWeightQpilotComparisonMissing where
  weightFamilyAgreement : Prop
  normalizationFactor : Prop
  logVolumeReading : Prop

/-- The exact weight-comparison gap. -/
def LGPBadWeightQpilotComparisonGap : Prop :=
  Nonempty LGPBadWeightQpilotComparisonMissing

#check lgpQpilotWeightSum
#check lgpQpilotBothNormalized_total
#check lgpBadNormalizedWeight_eq_qpilot_of_weightAgreement
#check LGPBadWeightQpilotComparisonGap

end LeanFormal.IUT.XiFPaper.S3136LGPBadWeightQpilotCompareActual
end