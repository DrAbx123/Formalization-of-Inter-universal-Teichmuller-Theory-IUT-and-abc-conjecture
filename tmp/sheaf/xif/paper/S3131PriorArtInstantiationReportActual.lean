import LeanFormal.IUT.Audit.Status

/-! # S3131 prior-art instantiation report: (b)/(c)/q-side - data only -/

namespace LeanFormal.IUT.XiFPaper.S3131PriorArtInstantiationReportActual

def S3131PriorArtInstantiationReport : List (String × String) :=
  [ ("CardAMPLThetaBoundSupply", "REUSE partial: supplies HULL upper bound (O1/O2/O3 + realVolume_le/ofReal_le_theta_of_imageSet_lower/exists_hull_eq_ofReal/of_realVolume_le). NOT (c): (c) needs the region-vs-(weight+hull) relative bound; CardAMPL bounds the hull term only"),
    ("HunitEpsilonTransferReduction", "ADAPT comparison-layer only: epsilon<->sharp ENNReal transfer reusable (cor312GapSupply_le_of_forall_pos_le_add + converse); NOT a geometric (c) supply; blocked by absence of unit-region/Haar datum under degree faithfulness (frozen refutations) and open route (iii)"),
    ("SourceQSideComparison", "REUSE: paper-faithful q-side value sourceQSideNormalizedValue (signed real); ENNReal q-slot degenerate for q<0; q-side comparison remains a NAMED hypothesis"),
    ("SourceImageHullVolume", "REUSE dictionary: sourceLocalLogDegree/sourcePointVolume/logDegree_one; (b) still needs uniform height-vs-volume comparison + finite hull/region volumes; degree-faithful hull volume top blocker"),
    ("IUT IV Estimates Section1/Section2/StepV*", "REUSE for class-B nodes (Prop 1.7 weights; Prop 2.1 elementary; Steps (v)/(vi) averages)"),
    ("concrete model (SourceUnitRegionHaarDataActual + IQCarrierConcreteModel)", "REUSE: task-72 model construction = prior art; our adaptations only") ]

theorem S3131PriorArtInstantiationReport_length : S3131PriorArtInstantiationReport.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.S3131PriorArtInstantiationReportActual