import LeanFormal.IUT.Audit.Status

/-! # S3137: prior-art inventory (iv) F4/clause chain and (v) Card/CTheta/hull real computations.

Source-only references to the HolomorphicHull layer; reuse classification.
-/

namespace LeanFormal.IUT.XiFPaper.S3137PriorArtF4HullActual

def S3137PriorArtF4Chain : List (String × String × String) :=
  [ ("hunit from epsilon-hull bound", "HunitEpsilonTransferReduction.lean:90/103/118 cor312GapSupply_hunit_of_epsilon_hullBound, cor312GapSupply_epsilon_hullBound_of_hunit, cor312GapSupply_sourceInterface_hunit_of_epsilon_hullBound", "REUSE: F4(b) unit-log-zero / hull scaling transfer already proved"),
    ("exists epsilon-hull bound iff exists degreeBound", "HunitEpsilonTransferReduction.lean:141 cor312GapSupply_exists_epsilon_hullBound_iff_exists_degreeBound_le_hullVolume", "REUSE"),
    ("degree-faithful non-existence", "HunitEpsilonTransferReduction.lean:166 cor312GapSupply_not_exists_epsilon_hullBound_of_degreeFaithful", "REUSE"),
    ("unit-region subset hull", "HunitEpsilonTransferReduction.lean:188 cor312GapSupply_sourceInterface_hunit_unitRegion_subset_hull", "REUSE"),
    ("vertex convexity assembly", "HullVertexConvexityAssembly.lean:119/136/155/217/277 cor312GapSupply_sourceInterface_hunit_of_vertexVolumeBound/_labelVolumeBound/_labelEpsilonBound; sourceHullVolume_le_vertices_of_convexVertexData; sourceHullVolume_eq_vertices_of_convexVertexData", "REUSE"),
    ("Obligation record", "HunitEpsilonTransferReduction.lean:214 cor312HunitEpsilonTransfer", "REUSE") ]

theorem S3137PriorArtF4Chain_length : S3137PriorArtF4Chain.length = 6 := rfl

def S3137PriorArtCardHull : List (String × String × String) :=
  [ ("hull volume top/zero dichotomy", "CardHullRealFinitePhaseGate.lean:71/105/120/137/155/171 sourceHullVolume_eq_top_of_exists_pos_logDegree, _eq_top_iff, _le_imageVolume_iff_lt_top, _lt_top_iff_forall_logDegree_nonpos, _toReal_eq_zero_of_eq_top", "REUSE"),
    ("edge normalization reduction", "CardHullRealEdgeNormalizationReduction.lean:97/233/269/289 sourceImageVolume, sourceHullVolume_le_imageVolume_of_productEdgeNormalization/_of_contraction_and_productEdgeNormalization, sourceImageVolume_lt_top", "REUSE"),
    ("generator nonpositivity", "CardHullRealGeneratorNonpositivity.lean:322/359/382/412 sourceImageLogDegree_nonpos_of_q_le_one, _nonpos_iff_q_le_one, sourceHullVolume_le_imageVolume_of_q_le_one_and_scaling", "REUSE"),
    ("geometry reduction", "CardHullRealGeometryReduction.lean:152/162/181/278/324 sourceHullVolume_eq_imageVolume_iff, _le_imageVolume_iff_forall_pointVolume_le, _of_generator_nonpos", "REUSE"),
    ("signed log volume + cor312 conclusion", "CardHullRealSignedLogVolume.lean:259/435/461 sourceHullVolume_eq_imageVolume_of_signedImageComparison, cor312OfSourceSignedHullComparison", "REUSE: F4/Card/CTheta hull real computation"),
    ("determinant log volume and CTheta lower bound", "HullDeterminantLogVolumeReduction.lean:501/536/560/569 hullLogVolumeRay, cor312CThetaLowerBound, cor312CThetaLowerBound_expTwo_satisfiable, cor312ComparisonData_nonempty", "REUSE: Cor 3.12 CTheta/hull supply"),
    ("Card/AMP theta bound supply", "CardAMPLThetaBoundSupply.lean:193 cor312Conclusion", "REUSE"),
    ("edge normalization dichotomy", "CardHullRealEdgeNormalizationDichotomy.lean:310/370/390/474 sourceHullVolume_eq_zero_of_hull_logDegree_nonpos, _le_imageVolume_iff_hull_logDegree_nonpos, cardHullRealEdgeNormalizationDichotomy", "REUSE") ]

theorem S3137PriorArtCardHull_length : S3137PriorArtCardHull.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.S3137PriorArtF4HullActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: prior-art inventory (iv)+(v). -/
def S3137PriorArtF4HullRecord : Obligation :=
  { id := "INDEX.PRIOR-ART.f4-clause-hull"
    source := "HunitEpsilonTransferReduction.lean; HullVertexConvexityAssembly.lean; CardHullReal* .lean; HullDeterminantLogVolumeReduction.lean; CardAMPLThetaBoundSupply.lean"
    status := VerificationStatus.interface
    note := "PRIOR ART (iv)+(v): the F4(b) clause chain (hunit/epsilon-hull/degree-faithful/unit-region-subset-hull/vertex convexity) and the Card/CTheta/hull real computations (top-zero dichotomy, edge normalization, generator nonpositivity, geometry reduction, signed log volume, determinant log volume, Cor 3.12 CTheta lower bound, Ampl theta supply) are ALREADY PROVED in HolomorphicHull. Reuse; do not rebuild. F4(a) realified identification and nontrivial scaling remain paper-input/formalization targets."
    dependsOn := ["S3137PriorArtF4HullActual"] }

end LeanFormal.IUT.Audit
