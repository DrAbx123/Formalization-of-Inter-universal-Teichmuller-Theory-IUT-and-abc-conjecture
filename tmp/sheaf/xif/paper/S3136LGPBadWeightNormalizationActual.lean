import tmp.sheaf.xif.paper.S3136LGPWeightAgreementBridgeActual

/-! # Stage-4 host: bad-weight normalization component (sum-one identity)

Source anchors: IUT II, Remark 2.5.1, (i); IUT III, Def. 3.8, (i) (p. 112-113);
IUT III, Remark 3.9.4 (realified log-volume normalization); IUT III, Prop. 3.9,
(i), p. 115.

This file constructs the actual normalized bad-weight family and proves the
sum-one identity (the R2-shape normalization condition) for the actual LGP
theta divisor weights:
* lgpBadWeightSum: the sum of the actual q_v divisor exponents as reals;
* lgpBadWeightSum_pos: positivity (from the actual positivity of each weight);
* lgpBadNormalizedWeight: the normalized bad weight;
* lgpBadNormalizedWeight_total: the normalized weights sum to 1;
* lgpBadNormalizedWeight_pos: each normalized weight is positive;
* LGPBadWeightNormalizationMissing/Gap: exact missing data (comparison with
  qpilot's actual normalization, log-volume normalization, mu-scaling fixed;
  refs above).

LABEL: prerequisite component only.  Consumer: lattice stream (R1/R-C),
IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPBadWeightNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.S3136LGPWeightAgreementBridgeActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The sum of the actual bad-place weights (q_v divisor exponents). -/
noncomputable def lgpBadWeightSum : ℝ :=
  ∑ b : Bad (nativePlaceSelection T), lgpBadWeight T b

/-- The actual bad-weight sum is positive when the bad family is nonempty. -/
theorem lgpBadWeightSum_pos [Nonempty (Bad (nativePlaceSelection T))] :
    0 < lgpBadWeightSum T := by
  unfold lgpBadWeightSum
  exact Finset.sum_pos (fun b _ => lgpBadWeight_pos T b) Finset.univ_nonempty

/-- The normalized bad weight. -/
noncomputable def lgpBadNormalizedWeight
    (b : Bad (nativePlaceSelection T)) : ℝ :=
  lgpBadWeight T b / lgpBadWeightSum T

/-- Each normalized bad weight is positive. -/
theorem lgpBadNormalizedWeight_pos [Nonempty (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T)) : 0 < lgpBadNormalizedWeight T b := by
  unfold lgpBadNormalizedWeight
  exact div_pos (lgpBadWeight_pos T b) (lgpBadWeightSum_pos T)

/-- The normalized bad weights sum to one (the R2-shape normalization
identity, proved for the actual LGP theta divisor weights). -/
theorem lgpBadNormalizedWeight_total [Nonempty (Bad (nativePlaceSelection T))] :
    (∑ b : Bad (nativePlaceSelection T), lgpBadNormalizedWeight T b) = 1 := by
  unfold lgpBadNormalizedWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (lgpBadWeightSum_pos T))

/-- Exact missing data for the normalization component (IUT II, Remark 2.5.1,
(i); IUT III, Def. 3.8, (i); Remark 3.9.4; Prop. 3.9, (i)):
* qpilotNormalizationComparison: comparison of the actual LGP normalized
  weights with qpilot's actual normalization (S3131NormalizedWeight family);
* logVolumeNormalization: the realified log-volume normalization identity of
  Remark 3.9.4 / Prop. 3.9(i);
* muScalingFixed: the mu_{2l}-scaling behaviour of the normalization. -/
structure LGPBadWeightNormalizationMissing where
  qpilotNormalizationComparison : Prop
  logVolumeNormalization : Prop
  muScalingFixed : Prop

/-- The exact normalization gap. -/
def LGPBadWeightNormalizationGap : Prop :=
  Nonempty LGPBadWeightNormalizationMissing

#check lgpBadWeightSum_pos
#check lgpBadNormalizedWeight_pos
#check lgpBadNormalizedWeight_total
#check LGPBadWeightNormalizationGap

end LeanFormal.IUT.XiFPaper.S3136LGPBadWeightNormalizationActual
end