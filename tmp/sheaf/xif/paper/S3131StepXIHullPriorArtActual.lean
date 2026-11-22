import LeanFormal.IUT.Audit.Status

/-! # S3131 StepXI/HolomorphicHull prior art inventory - data only -/

namespace LeanFormal.IUT.XiFPaper.S3131StepXIHullPriorArtActual

def S3131StepXIHullPriorArt : List (String × String) :=
  [ ("CardAMPLThetaBoundSupply.lean:94 realVolume_le; :101 ofReal_le_theta_of_imageSet_lower; :109 exists_hull_eq_ofReal; :116 of_realVolume_le; :125 nonempty_iff; :135 singletonRealSupply", "(c) upper-bound supply -> REUSE/ADAPT"),
    ("HunitEpsilonTransferReduction.lean:62/:70 cor312GapSupply_le_of_forall_pos_le_add; :90 cor312GapSupply_hunit_of_epsilon_hullBound; :103 converse; :118 sourceInterface version", "(c) gap supply + hunit/epsilon transfer -> REUSE (directly about Gap 2 fields)"),
    ("SourceQSideComparison.lean:71 iqHullCertificate_hqSlot_of_neg; :88 sourceQSideNormalizedValue; :96 eq_iSup_sourceQSide; :108 ge_sourceQSide; :125 ge_ofReal_of_sourceQSide_le; :140 neg_iff", "q-side comparison -> REUSE"),
    ("SourceImageHullVolume.lean:81 sourceVolumeIndexEquiv; :87 finite; :92 card_pos; :103 sourceLocalLogDegree; :107 sourcePointVolume; :110 sourceLocalLogDegree_one", "log-volume/dictionary -> REUSE"),
    ("HullDeterminantLogVolumeReduction.lean:153 hullDeterminantLogVolumeFrozenSpec_holds; :173 matrixLogDet; :179/:187/:197/:213 log-det laws", "hull determinant log-volume -> REUSE"),
    ("CardHullReal* files (EdgeNormalization*, FinitePhaseGate, GeneratorNonpositivity, GeometryGapCards/Reduction, HaarDilationDocking, SignedLogVolume)", "signed log-volume/geometry reductions -> REUSE/ADAPT"),
    ("SourceUnitRegionHaarDataActual.lean:122/146/151/213/288/322/346 + :374/:407/:416", "CONCRETE MODEL ALREADY IN TREE -> REUSE (task-72 prior art)"),
    ("IQCarrierConcreteModel.lean", "concrete IQ carrier + 5 unconditional inputs + epsilonComparison assembly -> REUSE (gate-v4-I instantiates over sourceHaarActualOriginalInput)") ]

theorem S3131StepXIHullPriorArt_length : S3131StepXIHullPriorArt.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.S3131StepXIHullPriorArtActual