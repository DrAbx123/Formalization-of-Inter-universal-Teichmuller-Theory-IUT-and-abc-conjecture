/-! # Stage-4 host: prior-art Cor312 Gap-2 supply signatures (§7.9 check)

PRIOR ART (checked before writing):
* LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HunitEpsilonTransferReduction.lean:
  :62 cor312GapSupply_le_of_forall_pos_le_add; :70 cor312GapSupply_forall_pos_le_add_of_le;
  :90 cor312GapSupply_hunit_of_epsilon_hullBound (v R n D D0 hD0 hε : forall eps>0,
  ofReal D.degreeBound <= sourceHullVolume v R n + ofReal D0 + eps);
  :103 cor312GapSupply_epsilon_hullBound_of_hunit (converse);
  :118 cor312GapSupply_sourceInterface_hunit_of_epsilon_hullBound (consumer drop-in);
  :141 cor312GapSupply_exists_epsilon_hullBound_iff_exists_degreeBound_le_hullVolume;
  :166 cor312GapSupply_not_exists_epsilon_hullBound_of_degreeFaithful (FROZEN REFUTATION);
  :188 cor312GapSupply_sourceInterface_hunit_unitRegion_subset_hull (conditional route (i)).
* CardAMPLThetaBoundSupply.lean: :78 structure CardAMPLThetaBoundSupply {X} (W :
  IQHullLogVolumeInterface X) {theta : Real; theta_nonneg : 0 <= theta;
  hull_logVolume_le : W.logVolume W.hull <= ofReal theta};
  :94 realVolume_le; :101 ofReal_le_theta_of_imageSet_lower; :109 exists_hull_eq_ofReal;
  :116 of_realVolume_le (converse constructor); :125 nonempty_iff; :193 cor312Conclusion.
* IUTIV/Estimates/StepVProcessionAverage.lean: :35 collectionBound l D Q S T j =
  (j+1)D - j^2/(2l) Q + S + 4(j+1)T; :39 sum_collectionBound; :54 processionAverage_eq;
  :68 processionAverage_le; :100 exceptionalSum_le_r4 ((R4)); :125 collectionChoiceBound;
  :162 weightedAverage_labelBeta; :190 weightedAverage_le_collectionBound;
  :217 processionNormalized_le_of_collectionBounds.

DETERMINATION (data rows): the Hunit comparison IS exactly the unit-region-bound shape
of our (c) split: degreeBound plays the normalized-weight/unit-region bound role and
sourceHullVolume plays the region-log-volume role.  CardAMPLThetaBoundSupply supplies
the Theta-constant upper bound side (real form iqHullRealVolume <= theta).  The
weighted-average side (Prop 1.7 / Step V) is StepVProcessionAverage collectionBound +
processionAverage_le; (R4) is exceptionalSum_le_r4.  Carrier caveat: these are
log-volume/interface carriers, not the native Haar measure carrier of
lgpNativeHaarFamily, so direct instantiation of our LGPRegionVolumeBound requires a
carrier bridge (recorded, not claimed).

LABEL: prior-art signature data. Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136PriorArtCor312SuppliesActual

structure LGPPriorArtSupplyRow where
  file : String
  declaration : String
  signatureOrFields : String
  supplies : String
  decision : String

def lgPPriorArtCor312Supplies : List LGPPriorArtSupplyRow :=
  [ ⟨"HunitEpsilonTransferReduction.lean", "cor312GapSupply_le_of_forall_pos_le_add (:62)", "∀ ε : NNReal, 0<ε → a ≤ b+ε → a ≤ b (a,b : ENNReal)", "epsilon-to-sharp transfer", "REUSE"⟩,
    ⟨"HunitEpsilonTransferReduction.lean", "cor312GapSupply_hunit_of_epsilon_hullBound (:90)", "v R n D D0, hD0:0<=D0, hε per-eps ofReal D.degreeBound <= sourceHullVolume + ofReal D0 + eps", "unit-region bound -> hunit (epsilon form)", "REUSE (exact unit-region supply shape)"⟩,
    ⟨"HunitEpsilonTransferReduction.lean", "cor312GapSupply_epsilon_hullBound_of_hunit (:103)", "sharp comparison -> per-eps form", "converse (logical equivalence)", "REUSE"⟩,
    ⟨"HunitEpsilonTransferReduction.lean", "cor312GapSupply_sourceInterface_hunit_of_epsilon_hullBound (:118)", "consumer drop-in with eps form for the source interface hunit slot", "discharges hunit slot", "REUSE"⟩,
    ⟨"HunitEpsilonTransferReduction.lean", "cor312GapSupply_not_exists_epsilon_hullBound_of_degreeFaithful (:166)", "under pointwise degree faithfulness no SourceUnitRegionHaarData satisfies the comparison", "FROZEN REFUTATION: nondegenerate source-hull datum impossible", "HONESTY: do not claim nondegenerate instantiation"⟩,
    ⟨"CardAMPLThetaBoundSupply.lean", "structure CardAMPLThetaBoundSupply (:78)", "theta : Real; theta_nonneg : 0<=theta; hull_logVolume_le : W.logVolume W.hull <= ofReal theta", "Theta-constant upper bound side of Cor 3.12", "REUSE (Theta upper-bound supply)"⟩,
    ⟨"CardAMPLThetaBoundSupply.lean", "realVolume_le (:94), ofReal_le_theta_of_imageSet_lower (:101), exists_hull_eq_ofReal (:109), of_realVolume_le (:116), nonempty_iff (:125)", "real/ENNReal reformulations of the supply", "reduction laws and converse", "REUSE"⟩,
    ⟨"StepVProcessionAverage.lean", "collectionBound (:35) + sum_collectionBound (:39) + processionAverage_eq (:54) + processionAverage_le (:68)", "collectionBound l D Q S T j = (j+1)D - j^2/(2l)Q + S + 4(j+1)T; average = (l+5)/4 D - (l+1)/24 Q + S + (l+5)T; <= (l+1)/4{(1+4/l)D - Q/6 + 4/l S + 20/3 T}", "weighted-average side (IV L1736-1783; Prop 1.7 shape)", "REUSE (weighted-average supply)"⟩,
    ⟨"StepVProcessionAverage.lean", "exceptionalSum_le_r4 (:100)", "sum_{I*} (3+log e_i) <= 4|I| iota log(e*_mod l) under p<=e*_mod l and log e_i <= -3+4log(e*_mod l)", "(R4) exceptional-term estimate (part of the split-point side)", "REUSE (partial split-point supply)"⟩,
    ⟨"StepVProcessionAverage.lean", "weightedAverage_le_collectionBound (:190) + processionNormalized_le_of_collectionBounds (:217)", "weighted averages over labels and procession-normalized bound", "weighted-average end-to-end", "REUSE"⟩ ]

theorem lgPPriorArtCor312Supplies_length : lgPPriorArtCor312Supplies.length = 10 := rfl

#check lgPPriorArtCor312Supplies
#check lgPPriorArtCor312Supplies_length

end LeanFormal.IUT.XiFPaper.S3136PriorArtCor312SuppliesActual