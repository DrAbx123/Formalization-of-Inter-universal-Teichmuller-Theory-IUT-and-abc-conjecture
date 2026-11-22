/-! # Stage-4 host: joint (c) status table — region side (stage4) x theta side (abc)

PRIOR ART (checked first): S3135RegionRelativeIQActual:14/:27 (abc's theta W-form at
the tree's iqCarrierModelInterface, remaining weight <= S.theta);
S3136Gap2AdditiveWiringActual (stage4's wired gap2: hunit actual, hsplit/hptfin from
membership, hpoint from GapDictionaryLayer:372 approved additive input);
S3136RegionRelativeReconciliationActual (consumed-hypothesis reconciliation).

CONSUMER: mainline joint status.  Data table of the two complementary sides, the exact
hypothesis each consumes, and the exact residual per side.  No discharge claim.

LABEL: joint status table (data). Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136AbcJointCObligationStatusActual

structure LGPJointCObligationRow where
  side : String
  form : String
  consumed : String
  residual : String

def lgpJointCObligationStatus : List LGPJointCObligationRow :=
  [ ⟨"abc / theta side",
      "S3135RegionRelativeToHullAndWeightW W weight theta := hull <= ofReal theta and hull < top and weight <= theta",
      "CardAMPLThetaBoundSupply.hull_logVolume_le (+ finiteness); EXACT residual: weight <= S.theta (IV section 2 normalization/weight input)",
      "weight <= S.theta; provider S.theta at iqCarrierModelInterface"⟩,
    ⟨"stage4 / region side",
      "exists D, region.toReal <= (1+eps)*weight + hull.toReal + D (conclusion of Cor312ComparisonGapReduction:306)",
      ":306 consumes hunit, hsplit, hptfin, hpoint (NOT theta/weight bound)",
      "hpoint from approved additive input: hadd (height <= (1+eps)weight + A), hline (degree <= height), hmem (membership); hunit/hsplit/hptfin WIRED"⟩,
    ⟨"joint bridge",
      "theta form: exists D, region.toReal <= (1+eps)*theta + hull.toReal + D",
      "lgpRegionVolumeBound_theta_form (class A) + abc's weight <= theta",
      "same residual as region side plus weight <= theta"⟩ ]

theorem lgpJointCObligationStatus_length : lgpJointCObligationStatus.length = 3 := rfl

#check lgpJointCObligationStatus
#check lgpJointCObligationStatus_length

end LeanFormal.IUT.XiFPaper.S3136AbcJointCObligationStatusActual