import Mathlib.Tactic

/-!
# A838 Gap-supply layer audit: does the ABCBridge/Bridge layer construct the gap supply?

Files read (all green, oleans present):
* `LeanFormal/IUT/ABCBridge/Bridge/Cor312ComparisonGapReduction.lean`
* `LeanFormal/IUT/ABCBridge/Bridge/Cor312ComparisonGapSupplyLayer.lean`
* `LeanFormal/IUT/ABCBridge/Bridge/Cor312GapDictionaryLayer.lean`
* `LeanFormal/IUT/ABCBridge/Bridge/Cor312PointwiseMembershipWeakening.lean`
* `LeanFormal/IUT/ABCBridge/Bridge/Cor312PointwiseResidualSupply.lean`
* `LeanFormal/IUT/ABCBridge/Bridge/Cor312CarrierRealizationSpec.lean`

**Answer: the gap supply is NOT constructed.**  The files provide:
* reduction of the two named comparison-gap fields to five named inputs
  (`hunit`, `hsplit`, `hptfin`, `hweightvol`, `hpoint`); the assembly is conditional and
  the audit record says explicitly `NOT proved: any of the five named inputs, and no claim
  that the gap fields are filled` (`cor312ComparisonGapReductionObligation`);
* supply of `hsplit`/`hptfin` for the *value-realized* interface (conditional on
  `SourceUnitRegionHaarData`), while `hunit`, `hweightvol` (degree-weight dictionary) and
  `hpoint` (point-volume/height) remain open/gap;
* dictionary-layer theorems and negative results (weight/point-height dictionaries are not
  universal: `cor312GapDict_weightDictionary_not_universal`,
  `cor312GapDict_pointHeightDictionary_not_universal`);
* weakening-layer conditional ABC (`abcConjecture_of_frontierPointwiseWeakened`) from a
  weaker frontier statement, not a gap construction;
* pointwise residual supply only for point finiteness, with a negative universal statement
  (`cor312Pointwise_not_forall_singleton_logVolume_lt_top`);
* a carrier-realization spec that is NOT inhabited (`cor312CarrierSpec_not_inhabited`).

Relation to our `Mzk1ABCTwoEstimates`: **no Lean equivalence and no bridge theorem exists**.
Our object is a pair of height/volume estimates over all ABC triples
(`height_estimate`, `volume_estimate`), while these files work with comparison gaps
`arithmeticWeight <= logVolume`/point-volume dictionaries.  The mapping is a *named
dictionary* (PENDING), not proved; neither side implies the other in the current tree.

Verdict: **ABC 卡点未被这些文件解决**; the gap-supply layer is a conditional reduction/
interface, not a construction.  No fake discharge.

No RETRACTED statement is used.  No sorry/axiom/True.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GapSupplyAuditActual

structure AuditRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def auditRows : List AuditRow :=
  [ ⟨"Cor312ComparisonGapReduction", "reduces the 2 named gaps to 5 named inputs (hunit,hsplit,hptfin,hweightvol,hpoint); assembly conditional; obligation says gap fields NOT filled", "CONDITIONAL_REDUCTION"⟩
  , ⟨"Cor312ComparisonGapSupplyLayer", "hsplit/hptfin supplied for value-realized interface (conditional on SourceUnitRegionHaarData); hunit/hweightvol/hpoint open; no gap field filled", "PARTIAL"⟩
  , ⟨"Cor312GapDictionaryLayer", "degree-weight/point-height dictionaries conditional; not universal (negative theorems)", "PARTIAL"⟩
  , ⟨"Cor312PointwiseMembershipWeakening", "conditional ABC from weaker frontier statement; no gap supply construction", "PARTIAL"⟩
  , ⟨"Cor312PointwiseResidualSupply", "point finiteness supply; universal singleton bound refuted", "PARTIAL"⟩
  , ⟨"Cor312CarrierRealizationSpec", "spec not inhabited (cor312CarrierSpec_not_inhabited)", "NO_SUPPLY"⟩
  , ⟨"our Mzk1ABCTwoEstimates", "height_estimate + volume_estimate over all ABC triples; abc_of_twoEstimates conditional on the two estimates", "DIFFERENT_OBJECT"⟩
  , ⟨"bridge between the two", "no Lean equivalence/implication proved; mapping is a named dictionary", "PENDING"⟩
  , ⟨"ABC card", "NOT resolved by these files; gap fields still named inputs", "NOT_RESOLVED"⟩
  ]

theorem auditRows_length : auditRows.length = 9 := rfl

theorem no_gap_supply_discharged :
    (auditRows.filter (fun r => r.status = "DISCHARGED")).length = 0 := by
  decide

theorem abc_card_not_resolved :
    auditRows.any (fun r => r.status = "NOT_RESOLVED") = true := by
  decide

theorem supply_layer_is_partial :
    (auditRows.filter (fun r => r.status = "PARTIAL")).length = 4 := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1GapSupplyAuditActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapSupplyAuditActual.no_gap_supply_discharged
#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapSupplyAuditActual.abc_card_not_resolved
