import LeanFormal.IUT.Audit.Status

/-! # S3131 class-B reuse plan: paper nodes -> in-tree formalized ingredients - data only -/

namespace LeanFormal.IUT.XiFPaper.S3131IUTIVEstimatesReusePlanActual

def S3131IUTIVEstimatesReusePlan : List (String × String) :=
  [ ("IUT IV Prop 1.7 weighted averages (class B)", "reuse Estimates/Section1.lean iutIVProp17_* (betaAvg/lambdaE_pow/weightedTupleSum/betaTupleSum/middle)"),
    ("IUT IV Prop 2.1 elementary (class A)", "reuse Estimates/Section2.lean iutIVProp21i_log_le_self + iutIVProp21ii_* + sixfoldBinomialProduct"),
    ("IUT IV Thm 1.10 Steps (v)/(vi) averages (class B)", "reuse Estimates/StepVProcessionAverage.lean (collectionBound/sum_collectionBound/processionAverage_eq/le) + StepVDivisorAverage + StepVDistinguishedSlotAverage"),
    ("(c) Gap 2 supply/transfer", "reuse HunitEpsilonTransferReduction.lean cor312GapSupply_hunit_of_epsilon_hullBound + converse + sourceInterface"),
    ("(c) upper bound supply", "reuse CardAMPLThetaBoundSupply.lean realVolume_le/ofReal_le_theta_of_imageSet_lower/of_realVolume_le"),
    ("q-side comparison", "reuse SourceQSideComparison.lean sourceQSideNormalizedValue + certificate slot lemmas"),
    ("dictionary/local log-degree", "reuse SourceImageHullVolume.lean sourceLocalLogDegree/sourcePointVolume + RationalPointDictionary/RationalPrimeSupport") ]

theorem S3131IUTIVEstimatesReusePlan_length : S3131IUTIVEstimatesReusePlan.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.S3131IUTIVEstimatesReusePlanActual