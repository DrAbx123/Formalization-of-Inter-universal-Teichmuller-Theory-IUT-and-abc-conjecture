namespace LeanFormal.IUT.XiFPaper.Node09GapDonorSurveyActual

/-- Donor survey for the two IV/ABC comparison gaps.  Each entry names the exact
Lean declaration and its status. -/
def Node09GapDonorSurvey : List (String × String) :=
  [ ("hsplit", "Proved for the value-realized carrier: Cor312ComparisonGapSupplyLayer.cor312GapSupply_sourceInterface_hsplit"),
    ("hptfin", "Proved for the value-realized carrier: Cor312ComparisonGapSupplyLayer.cor312GapSupply_sourceInterface_hptfin"),
    ("hunit", "Reduced to the degree-bound/hull-volume comparison: Cor312ComparisonGapSupplyLayer.cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume; satisfiable with the canonical constant max D.degreeBound 0 (Cor312CarrierRealizationSpec.cor312CarrierSpec_exists_hunitConstant), and absorbable into the additive constant of the conclusion"),
    ("hweightvol", "Reduced to the weight dictionary: Cor312ComparisonGapSupplyLayer.cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary; the weight dictionary is a genuine conditional input. Cor312GapDictionaryLayer.cor312GapDict_weightDictionary_not_universal assumes D+hdeg and is vacuous under the hull obstruction, so it neither proves nor refutes the actual-p dictionary"),
    ("hpoint", "Reduced to the point-height dictionary: Cor312GapDictionaryLayer.cor312GapDict_sourcePointBound_of_degree_le_height; the point-height dictionary is a genuine conditional input. cor312GapDict_pointHeightDictionary_not_universal assumes D+hdeg and is vacuous under the hull obstruction; the direct point-volume card is the alternative") ]

/-- Exact paper-level residual inputs: no unconditional donor exists for the two
comparison gaps, and the two dictionary cards cannot coexist. -/
def Node09GapResidualPaperInputs : List String :=
  [ "The two dictionaries (weight dictionary and point-height dictionary) are jointly refutable: Cor312CarrierRealizationSpec.cor312CarrierSpec_dictionaries_jointly_refutable and cor312CarrierSpec_not_inhabited; at (1,2,3), arithmeticWeight = log 6 > log 3 = logHeight, so both cards cannot hold for one point map",
    "Therefore no unconditional or dictionary-only supply of gap 1 + gap 2 exists: hweightvol and hpoint must be replaced by a direct point-volume card (vol {scaleShift (logShellPoint a b c)}).toReal <= (1+eps)*arithmeticWeight + D1, compatible with the weight dictionary (task-level decision, not taken in the existing modules)",
    "hunit is not a residual card: Cor312CarrierSpec.cor312CarrierSpec_epsilonComparison_of_dictionaries canonicalizes it to max D.degreeBound 0 and absorbs it into the additive constant",
    "No map from the conditional paper312 endpoint (ExplicitPaper312Inequality A <= Lbar + Dbar) to the normalized region/height/weight dictionary is known; this remains the exact missing bridge" ]

end LeanFormal.IUT.XiFPaper.Node09GapDonorSurveyActual
