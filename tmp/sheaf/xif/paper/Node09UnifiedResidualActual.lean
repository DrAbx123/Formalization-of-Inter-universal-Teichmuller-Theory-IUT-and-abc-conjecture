namespace LeanFormal.IUT.XiFPaper.Node09UnifiedResidualActual

/-- Unified residual inventory for the Node09 cards/S3135 route.  Documentation
only; no inhabitant, no axiom. -/
def Node09UnifiedResidual : List (String × String) :=
  [ ("upper point-volume input", "Card P = S3135ActualPointWeightCard = Node09 hpoint family = frozen gap2 regionVolume_le_normalizedWeight (via singleton<=region monotonicity). This is a single paper-level input: singleton/region point volume <= (1+eps)*arithmeticWeight + D. Equivalences: Node09S3135ResidualMapActual.s3135_pointWeightCard_iff_node09HpointFamily, Node09Gap2ToCardsActual.hpoint_of_comparison"),
    ("weight dictionary", "hweightDictionary for the actual point map: arithmeticWeight <= sourceLocalLogDegree (D.scaling * p). Genuine conditional input; equivalent to the scaling-separated inequality (Node09WeightDictionaryScalingActual). The available degree-faithfulness status theorems assume D+hdeg and are vacuous under the hull obstruction, so the actual-p dictionary is neither proved nor refuted"),
    ("F4 card 1", "S3135PointLogShellFaithfulness: logDegreeAt (point height exponent) = height exponent; exact missing. Full value-group faithfulness S3135ValueGroupDegreeFaithfulness implies it; only cyclic log-q faithfulness is proved"),
    ("F4 card 2", "S3135ScalingLogDegreeZero: sourceLocalLogDegree v D.scaling = 0; exact missing. Carrier gives only <= 0; equivalently the normalized-scaling family S3135ScalingNormalization for every eps > 0"),
    ("discharged", "Card U S3135ActualUnitHullCard is unconditional (Node09S3135CardUActual); hsplit/hptfin are actual for the value-realized carrier; singleton<=region is monotonicity (Node09RegionMonoActual); hpoint follows from the frozen gap2 field (Node09Gap2ToCardsActual)"),
    ("conditional chain", "cards family -> Node09ComparisonCards -> Cor312ToABCBridgeInterface -> ABC height bound / ABCConjecture; all conditional, no inhabitant of the paper inputs"),
    ("no fake", "no inhabitant, no sorry, no new axiom; all residual entries are explicit paper-level inputs") ]

/-- The single upper input and the two F4 cards, plus the separate weight dictionary. -/
def Node09UnifiedResidualConclusion : List String :=
  [ "one new upper-bound paper input: Card P / Node09 hpoint / frozen gap2 (all the same statement)",
    "two F4 paper cards: S3135PointLogShellFaithfulness and S3135ScalingLogDegreeZero",
    "one separate lower-bound input: actual-p hweightDictionary in scaling-separated form",
    "everything else in the cards chain is discharged, actual, or conditional",
    "no unconditional ABC route exists (ABC inhabitant scan)" ]

end LeanFormal.IUT.XiFPaper.Node09UnifiedResidualActual
