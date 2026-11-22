namespace LeanFormal.IUT.XiFPaper.Node09HullConsistencyAuditActual

/-- Consistency audit of the Node09 cards chain against the hull obstruction
theorems.  Documentation only; no new hypothesis and no inhabitant. -/
def Node09HullConsistencyAudit : List String :=
  [ "obstruction 1: Cor312CarrierRealizationSpec.cor312CarrierSpec_dictionaries_jointly_refutable / cor312CarrierSpec_not_inhabited: the four-field package containing both the weight dictionary (c) and the point-height dictionary (d) is refutable, because (c)+(d) force arithmeticWeight <= logHeight on every ABC triple, false at (1,2,3)",
    "obstruction 2: HunitEpsilonTransferReduction.cor312GapSupply_not_exists_epsilon_hullBound_of_degreeFaithful and not_nonempty_valueHullCompactnessInput_of_degreeFaithful: degree faithfulness hdeg is incompatible with SourceUnitRegionHaarData/ValueHullCompactnessInput; equivalently sourceHullVolume = top under hdeg, contradicting the finite hull/unit data",
    "audit finding: the Node09 cards chain uses the direct point-volume card (singleton volume <= (1+eps)*weight + D1) plus the weight dictionary, NOT the point-height dictionary; therefore obstruction 1 does not refute the cards chain",
    "audit finding: Node09SourceCardsActual, Node09SingletonWeightActual, Node09Gap2SourceActual, Node09RegionMonoActual, Node09SingletonPointCardsActual, Node09ComparisonCardsActual and the final endpoints assume SourceUnitRegionHaarData D but do NOT assume hdeg; they are not inside the hdeg+D inconsistent premise space",
    "audit finding: the only Node09 file that assumes both D : SourceUnitRegionHaarData and hdeg is Node09DegreeUpperActual (exists_pointMap_degree_eq_weight / exists_pointMap_degree_le_weight). Under obstruction 2 this premise pair is inconsistent, so those theorems are vacuous; they have no importers and are not used by the cards chain. Flag: do not treat DegreeUpper as evidence for the actual point map; keep it out of the main chain",
    "audit finding: no other Node09 theorem assumes hdeg together with D; hweightDictionary and hdegreeBound in Node09SourceCardsActual are arbitrary source-data hypotheses, not hdeg",
    "consistency verdict: the cards chain is consistent conditional on D (without hdeg) and on the direct point-volume card/weight dictionary; the hull obstructions do not contradict it, and no theorem in the chain asserts an inhabitant of the two dictionaries or of SNamed/frozen gap2",
    "no fake; this audit does not prove consistency of D itself, only that no Node09 chain theorem uses the refuted hdeg+D or the refuted dictionary pair",
  "additional vacuity flag: all four cor312GapDict dictionary-status theorems require D and hdeg together: cor312GapDict_exists_pointMap_weightDictionary, cor312GapDict_exists_pointMap_pointHeightDictionary, cor312GapDict_weightDictionary_not_universal, cor312GapDict_pointHeightDictionary_not_universal. Under the hdeg+D obstruction their premise pair is inconsistent, so they are vacuous: they cannot be cited as evidence that the weight dictionary is satisfiable OR refutable for the actual point map",
  "the conditional criteria cor312GapDict_weightDictionary_iff_scalingSeparated / _implies_scalingFree do not require hdeg and are genuine; they reduce the actual-p weight dictionary to the scaling-separated inequality",
  "consequence: hweightDictionary for the actual point map is neither proved nor refuted by the current tree; it remains an exact paper-level input" ]

end LeanFormal.IUT.XiFPaper.Node09HullConsistencyAuditActual
