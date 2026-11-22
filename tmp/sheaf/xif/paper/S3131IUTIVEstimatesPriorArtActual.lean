import LeanFormal.IUT.Audit.Status

/-! # S3131 IUT IV Estimates prior art (class B ingredient inventory) - data only -/

namespace LeanFormal.IUT.XiFPaper.S3131IUTIVEstimatesPriorArtActual

def S3131IUTIVEstimatesPriorArt : List (String × String) :=
  [ ("Estimates/Section1.lean:115 iutIVProp17_betaAvg; :119 lambdaE_pow; :125 weightedTupleSum; :157 betaTupleSum; :172 middle", "IUT IV Prop 1.7 weighted-average machinery -> REUSE (class B)"),
    ("Estimates/Section2.lean:111 iutIVProp21i_log_le_self; :124/:190/:225 iutIVProp21ii_*; :252 sixfoldBinomialProduct", "IUT IV Prop 2.1 elementary bounds -> REUSE (class A)"),
    ("Estimates/StepVProcessionAverage.lean:35 collectionBound; :39 sum_collectionBound; :54 processionAverage_eq; :68 processionAverage_le; :100 exceptionalSum_le_r4; :125 collectionChoiceBound", "Thm 1.10 weighted averages / (R1)-(R3) side -> REUSE (class B)"),
    ("Estimates/StepVDivisorAverage.lean / StepVDistinguishedSlotAverage.lean", "distinguished-slot/divisor averages -> REUSE (class B)"),
    ("Estimates/ElementaryEstimates.lean / DifferentTowerEstimate.lean / DifferentDegreeUpperBound.lean", "elementary estimates / log-different tower bounds -> REUSE (class A/B)"),
    ("Estimates/ArchimedeanTensorMetric.lean / ArchimedeanMultiTensorMetric.lean / ArithmeticDivisorDegree.lean", "archimedean metrics + arithmetic divisor degree -> REUSE as needed") ]

theorem S3131IUTIVEstimatesPriorArt_length : S3131IUTIVEstimatesPriorArt.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.S3131IUTIVEstimatesPriorArtActual