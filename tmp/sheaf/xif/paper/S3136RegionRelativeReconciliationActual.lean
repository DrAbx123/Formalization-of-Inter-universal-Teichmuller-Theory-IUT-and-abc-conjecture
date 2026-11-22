import tmp.sheaf.xif.paper.S3135RegionRelativeIQActual
import tmp.sheaf.xif.paper.S3136Gap2AdditiveWiringActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardAMPLThetaBoundSupply

/-! # Stage-4 host: reconciliation of the A26/gap2 obligation form with abc's theta W-form

PRIOR ART (§7.9, checked first):
* Cor312ComparisonGapReduction.lean:306 gap2 reduction.  Its EXACT consumed hypotheses are
  (W, logShellPoint p, eps, D0>=0, D1) with
    hunit  : W.logVolume W.unitRegion <= W.logVolume W.hull + ofReal D0,
    hsplit : per-ABC-triple normalizedComparisonRegion volume <= scaled unit region volume +
             singleton(point) volume,
    hptfin : per-triple singleton(point) volume < top,
    hpoint : per-triple (singleton point volume).toReal <= (1+eps)*arithmeticWeight + D1.
  It does NOT consume any theta bound or weight bound; the conclusion is
    exists D, forall ABC triples, (region volume).toReal <= (1+eps)*weight + hull.toReal + D.
* abc's W-form (S3135RegionRelativeIQActual:14 S3135RegionRelativeToHullAndWeightW):
    W.logVolume W.hull <= ofReal theta  /\  W.logVolume W.hull < top  /\  weight <= theta,
  instantiated at iqCarrierModelInterface (s3135_regionRelative_iqCarrier) with the exact
  remaining hypothesis weight <= S.theta (IV section 2 normalization/weight input).
* CardAMPLThetaBoundSupply.lean:78 supplies the hull <= ofReal theta half.

RECONCILIATION: the two forms are complementary, not competing: abc's W-form is the
THETA/CERTIFICATE side (hull bounded by ofReal theta and weight <= theta), while the
gap2 form is the REGION-VOLUME side consuming hunit/hsplit/hptfin/hpoint.  Given a
gap2 obligation with weight and abc's weight <= theta, the region bound can be
rewritten in theta form (class A real transfer below).  Wiring of hunit/hsplit/hptfin
+ hpoint from the approved additive input is S3136Gap2AdditiveWiringActual.

LABEL: reconciliation (data + class A transfer); no discharge claims. Registry frozen;
new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136RegionRelativeReconciliationActual

open LeanFormal.IUT

variable {X : Type*} {W : IQHullLogVolumeInterface X}
variable (p : Nat → Nat → Nat → X)

/-- The A26/gap2 region-volume obligation form (exactly the conclusion shape of
`cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound`). -/
def LGPRegionVolumeObligation (eps D : ℝ) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    (W.logVolume (normalizedComparisonRegion W p a b c)).toReal ≤
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
        (W.logVolume W.hull).toReal + D

/-- The consumed-hypothesis record of the gap2 reduction (data rows). -/
def lgpGap2ConsumedHypotheses : List (String × String) :=
  [ ("hunit", "W.logVolume W.unitRegion <= W.logVolume W.hull + ENNReal.ofReal D0 (D0>=0)"),
    ("hsplit", "per-triple region volume <= scaled-unit volume + singleton point volume"),
    ("hptfin", "per-triple singleton point volume < top"),
    ("hpoint", "per-triple singleton volume.toReal <= (1+eps)*arithmeticWeight + D1"),
    ("NOT consumed", "theta bound / weight <= theta (these belong to abc's W-form and certificates)") ]

theorem lgpGap2ConsumedHypotheses_length : lgpGap2ConsumedHypotheses.length = 5 := rfl

/-- Class A real transfer: replacing weight by theta in a region-volume bound. -/
theorem lgpRegionVolumeBound_theta_form {R weight H theta D eps : ℝ}
    (heps : 0 ≤ eps) (hweightθ : weight ≤ theta)
    (h : R ≤ (1 + eps) * weight + H + D) :
    R ≤ (1 + eps) * theta + H + D := by
  nlinarith

/-- Pointwise theta-form of a region-volume obligation given weight <= theta per triple. -/
theorem lgpRegionVolumeObligation_theta_form {eps D : ℝ} (heps : 0 ≤ eps)
    (theta : ℝ)
    (hob : LGPRegionVolumeObligation (W := W) p eps D)
    (hweightθ : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤ theta) :
    ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (normalizedComparisonRegion W p a b c)).toReal ≤
        (1 + eps) * theta + (W.logVolume W.hull).toReal + D := by
  intro a b c habc
  exact lgpRegionVolumeBound_theta_form heps (hweightθ a b c habc) (hob a b c habc)

#check LGPRegionVolumeObligation
#check lgpGap2ConsumedHypotheses_length
#check lgpRegionVolumeBound_theta_form
#check lgpRegionVolumeObligation_theta_form

end LeanFormal.IUT.XiFPaper.S3136RegionRelativeReconciliationActual
end