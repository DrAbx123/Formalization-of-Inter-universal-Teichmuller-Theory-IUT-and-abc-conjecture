/-! # Stage-4 host: exact prior-art shapes of the (c) split-point/unit-region obligations

PRIOR ART (§7.9, checked first; exact statements from the repo):
* Cor312ComparisonGapReduction.lean:306
  cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound
  with named inputs hunit, hsplit, hptfin, hpoint (see rows below);
  :409 cor312Gap2_hsplit_of_mem_unitRegion (hsplit from point membership);
  :432 cor312Gap2_hptfin_of_mem_unitRegion (hptfin from point membership);
  :455 cor312Gap2_pointBound_of_singletonVolume_le_logHeight (hpoint from volume/height);
  :525 realLineHullData_pointBound_of_valuation_bound; :599 assembly of additive inputs.
* Cor312GapDictionaryLayer.lean:34/:39 directions (weightDictionary iff scalingSeparated;
  implies scalingFree) and :368 cor312GapDict_sourcePointBound_of_additiveBound.
* Cor312ComparisonGapSupplyLayer.lean:271 cor312GapSupply_sourceGap1_of_additiveBound_degreeDictionary.
* StepXI CertificateHullWiring.lean:173 hull_le_theta (iqHullCertificate slot), :199
  target_le_theta (iqHullLinkEvidence), :301 sourceThetaBound_unsat_of_degreeFaithful
  (interface-correction refutation).
* IUTIV/Estimates/ElementaryEstimates.lean:76-146 e1-e6 (arithmetic means, GL2 order,
  adjoin sqrt(-1) finrank, log bounds) - all formalized.

CONSUMER: mainline's (c) obligation wiring.  This data file records the EXACT named
hypothesis shapes of the gap-2 reduction so the (c) slots can be filled by whichever
producer exists (old-attempt hunit/hsplit/hptfin on the S2586 carrier; additive input
for hpoint; certificates for theta bound).  No discharge is claimed here.

LABEL: exact shapes (data). Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136SplitPointPriorArtExactActual

structure LGPGap2InputRow where
  input : String
  exactShape : String
  priorArtProducer : String

def lgpGap2Inputs : List LGPGap2InputRow :=
  [ ⟨"hunit", "W.logVolume W.unitRegion <= W.logVolume W.hull + ENNReal.ofReal D0", "old attempt S2722_hunitD (actual D0) / Hunit transfer (epsilon form)"⟩,
    ⟨"hsplit", "forall ABC triples, W.logVolume (normalizedComparisonRegion W p a b c) <= W.logVolume (W.scaleShift '' W.unitRegion) + W.logVolume {W.scaleShift (p a b c)}", "S2720BridgeHaarActual:70 (S2586 carrier) / cor312Gap2_hsplit_of_mem_unitRegion:409"⟩,
    ⟨"hptfin", "forall ABC triples, W.logVolume {W.scaleShift (p a b c)} < top", "singleton-null (S2586 carrier) / cor312Gap2_hptfin_of_mem_unitRegion:432"⟩,
    ⟨"hpoint", "(W.logVolume {W.scaleShift (p a b c)}).toReal <= (1+eps)*arithmeticWeight + D1", "cor312Gap2_pointBound_of_singletonVolume_le_logHeight:455 / :525 valuation bound / gap dictionary :368 additive bound (OPEN)"⟩,
    ⟨"hpoint (paper shape)", "same with the paper point log-volume (not degenerate)", "MISSING: no nondegenerate producer; singleton-null is degenerate"⟩,
    ⟨"theta upper bound", "W.logVolume W.hull <= ENNReal.ofReal theta", "CardAMPLThetaBoundSupply:78 fields / CertificateHullWiring:173 hull_le_theta"⟩,
    ⟨"theta bound refutation", "not exists theta under degree faithfulness", "CertificateHullWiring:301 sourceThetaBound_unsat_of_degreeFaithful"⟩,
    ⟨"weighted averages", "collectionBound sum/average bounds (IV L1736-1783)", "StepVProcessionAverage:35/54/68 (+ ElementaryEstimates e1/e2 means)"⟩ ]

theorem lgpGap2Inputs_length : lgpGap2Inputs.length = 8 := rfl

#check lgpGap2Inputs
#check lgpGap2Inputs_length

end LeanFormal.IUT.XiFPaper.S3136SplitPointPriorArtExactActual