namespace LeanFormal.IUT.XiFPaper.Node09FrozenGap2InvestigationActual

/-- Investigation summary: the frozen gap2 region-volume field is the sole
paper-level input, and its exact named forms are documented. -/
def Node09FrozenGap2Investigation : List String :=
  [ "frozen gap2 field: Cor312EpsilonArithmeticComparison.regionVolume_le_normalizedWeight, i.e. exists D, forall ABC triples, (logVolume region).toReal <= (1+eps)*weight + (logVolume hull).toReal + D",
    "equivalent named local-estimate form: Mzk1GapCorrespondenceAuditQpilotActual.gap2_iff_bridge, with localEstimateOfRegion W logShellPoint a b c = (logVolume normalizedComparisonRegion).toReal",
    "equivalent ENNReal named estimate: Mzk1ABCBridgeGap2ConsumerActual.SNamed regionVolume eps weight theta D := regionVolume <= ofReal ((1+eps)*weight + theta + D); gap2_real_bound and gap2_ennreal_bound convert between SNamed and the real form",
    "conditional reduction: Mzk1ABCBridgeGap2Conditional.gap2_conditional_reduction turns SNamed plus nonnegativity into the real-form region bound",
    "P7 section 9.1/9.2 gives the q-ideal product volume V(J_q;C_q) = -sum_b n_b f_b log p_b (weighted M_q), but there is no formal containment/volume comparison from that local-ideal product to the value-monoid normalizedComparisonRegion",
    "no producer of regionVolume_le_normalizedWeight / localEstimate_le_weight / SNamed exists in the current tree: the only provider is the reduced conditional cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound, whose hpoint/hunit inputs are the paper-level estimates",
    "therefore the frozen gap2 region-volume estimate remains the sole new paper-level input; no inhabitant and no fake is introduced" ]

end LeanFormal.IUT.XiFPaper.Node09FrozenGap2InvestigationActual
