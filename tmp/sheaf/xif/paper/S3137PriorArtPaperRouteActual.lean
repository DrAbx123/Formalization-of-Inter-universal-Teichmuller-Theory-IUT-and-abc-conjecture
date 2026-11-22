import LeanFormal.IUT.Audit.Status

/-! # S3137: prior-art inventory (vi) Cor312 comparison & card hull supply,
(vii) (b) height / (c) region-bound ingredients, (viii) Q-side comparison. -/

namespace LeanFormal.IUT.XiFPaper.S3137PriorArtPaperRouteActual

def S3137PriorArtCor312 : List (String × String × String) :=
  [ ("comparisonRegion + normalizedComparisonRegion", "LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean:200-251 normalizedComparisonRegion; :256-259 comparisonRegion accessor", "REUSE: construction is definitional; only logShellPoint + two gap fields remain"),
    ("region f/k finiteness", "Cor312ToABCBridgeInterface.lean:267-284 comparisonRegion_logVolume_lt_top", "REUSE"),
    ("additive V2 height form", "Cor312ToABCBridgeInterface.lean:319-392 Cor312EpsilonArithmeticComparisonAdditive + cor312ToABCBridge_heightBound", "REUSE: V2 additive shape is the paper-faithful height field"),
    ("gap-2 reductions", "Cor312ComparisonGapReduction.lean:128-306 cor312Gap2_hull_logVolume_le_normalizedComparisonRegion, _scaleShift_unitRegion_..., _regionVolume_le_add_of_subadditive, _regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound", "REUSE"),
    ("gap-1 conditional reduction + counterexample", "Cor312ComparisonGapReduction.lean:198/232/272 cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound; cor312Gap1_exists_carrier_arithmeticWeight_gt_...; cor312Gap1_not_forall_...", "REUSE: conditional; uniform forms REFUTED (kept negative)"),
    ("gap assembly", "Cor312ComparisonGapReduction.lean:367 cor312GapAssembly_epsilonComparisonOfReducedInputs", "REUSE"),
    ("dictionary non-universality + positive reductions", "Cor312GapDictionaryLayer.lean:176/200/230/268/338/372 cor312GapDict_weightDictionary_iff_scalingSeparated, _exists_pointMap_weightDictionary, _weightDictionary_not_universal, _sourcePointBound_of_degree_le_height, _of_additiveBound", "REUSE: dictionary is a genuine hypothesis, not a theorem"),
    ("point bound from singleton volume", "Cor312ComparisonGapReduction.lean:455/478 cor312Gap2_pointBound_of_singletonVolume_le_logHeight, realLineHullData_singletonVolume_eq_logHeight", "REUSE"),
    ("theta/CTheta/card supply into Cor312", "CardAMPLThetaBoundSupply.lean:193 cor312Conclusion; HullDeterminantLogVolumeReduction.lean:569 cor312ComparisonData_nonempty; CardHullRealSignedLogVolume.lean:435 cor312OfSourceSignedHullComparison", "REUSE") ]

theorem S3137PriorArtCor312_length : S3137PriorArtCor312.length = 9 := rfl

def S3137PriorArtHeightRegionQSide : List (String × String × String) :=
  [ ("(b) height/logHeight dictionary", "Height.logHeight₁ + abcRationalPoint_logHeight₁ (production ABCBridge dictionary files, e.g. RationalPointDictionary.lean)", "REUSE: accepted dictionary facts"),
    ("(b) additive height/weight reduction", "ABCHeightArithmeticWeightComparison.ABCHeightWeightAdditiveBoundV2 + heightWeightBound_of_normalizedVolumeComparison", "REUSE: V2 height shape (uniform V1 refuted)"),
    ("(c) hull theta bound", "Cor312EpsilonArithmeticComparison.regionVolume_le_normalizedWeight (thetaBound = (W.logVolume W.hull).toReal); IQCarrierHaarData.lean:207 hull volume finite; HunitEpsilonTransferReduction hunit chain", "REUSE: theta bound finite; per-triple region bound remains paper-route field"),
    ("(c) arithmetic weight side", "arithmeticWeight + arithmeticWeight_nonneg (rational prime support dictionary)", "REUSE"),
    ("Q-side comparison", "S3131PaperNormalizedComparisonActual.S3131PaperRegionalQ_le_Hull; S3131QCLeHCComparisonActual; S3137 qTheta bridge (qThetaPilotLogVolumeComparison_of_sameC/_of_modelMap)", "REUSE: unconditional paper-normalized comparison; sameC readout bridge is the S3137 residual"),
    ("Q-side positivity", "S3137QThetaPilotLogVolumeReadingsActual.qPilotLogVolumeReading_nonpos/_eq_neg_abs_qParameter", "REUSE") ]

theorem S3137PriorArtHeightRegionQSide_length :
    S3137PriorArtHeightRegionQSide.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.S3137PriorArtPaperRouteActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: prior-art inventory (vi)+(vii)+(viii). -/
def S3137PriorArtPaperRouteRecord : Obligation :=
  { id := "INDEX.PRIOR-ART.paper-route"
    source := "Cor312ToABCBridgeInterface.lean; Cor312ComparisonGapReduction.lean; Cor312GapDictionaryLayer.lean; Cor312GapDictionaryLayer; ABCHeightArithmeticWeightComparison; S3131/S3137 qTheta; CardAMPLThetaBoundSupply; HullDeterminantLogVolumeReduction"
    status := VerificationStatus.interface
    note := "PRIOR ART (vi)+(vii)+(viii): Cor312 comparison region/accessor, region finiteness, additive V2 height form, gap-2 reductions + gap-1 conditional reduction (uniform refuted), gap assembly, dictionary non-universality, point-bound-from-singleton, card/hull supply into Cor312, height dictionary, arithmetic weight, Q-side unconditional comparison and qPilot positivity are ALREADY available. Remaining: logShellPoint as actual object + nontrivial dictionary/point bound (paper input) and sameC readout bridge (S3137). Reuse; no rebuilding."
    dependsOn := ["S3137PriorArtPaperRouteActual"] }

end LeanFormal.IUT.Audit
