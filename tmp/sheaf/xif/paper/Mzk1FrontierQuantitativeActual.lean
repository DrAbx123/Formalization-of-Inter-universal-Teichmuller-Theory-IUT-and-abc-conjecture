import Mathlib.Tactic

/-!
# A841 quantitative decomposition of the ABCFrontier clauses (shehdd)

Read: `ABCFrontier.lean` (F4/F5), `ABCFrontierReductions.lean` (F4a/F4b/F5a–F5d/P1/P2),
`ABCFrontierPointwisePremiseReduction.lean`, `ABCFrontierHeightWeightRefutation.lean`,
`Cor312ComparisonGapReduction.lean` (gates :198, :306, :367, :409, :432, :455, :502, :557),
`Cor312ComparisonGapSupplyLayer.lean` (hsplit/hptfin/hunit/hweightvol/hpoint),
`Cor312GapDictionaryLayer.lean`, `Cor312PointwiseResidualSupply.lean`.

Notation: `W : IQHullLogVolumeInterface X`, `point ε hε a b c : X` is the named point,
`logVol` is `W.logVolume`, `D0/D1` are additive slacks, `ε>0`, `(a,b,c)` ABC triple.

## Exact quantitative clauses (all as in the files)
* F4/FrontierHeightComparisonClause:
  `∀ε>0 ∀abc, logHeight₁(abc) ≤ (1+ε)·logVol(normalizedComparisonRegion W (point ε) abc)`.
* F5/FrontierRegionComparisonClause:
  `∀ε>0 ∃D, ∀abc, logVol(normalizedComparisonRegion W (point ε) abc) ≤
     (1+ε)·arithmeticWeight(abc) + logVol(W.hull) + D`.
* F4a/FrontierHeightWeightClause:
  `∀ε>0 ∀abc, logHeight₁ ≤ (1+ε)·arithmeticWeight` (no additive slack).
* F4b/FrontierWeightRegionClause:
  `∀ε>0 ∀abc, arithmeticWeight ≤ logVol(normalizedComparisonRegion W (point ε) abc)`.
* F5a/FrontierUnitNormalizationClause:
  `∃D0 ≥ 0, logVol(W.unitRegion) ≤ logVol(W.hull) + ofReal D0`.
* F5b/FrontierSplitClause:
  `∀ε>0 ∀abc, logVol(region) ≤ logVol(W.scaleShift '' W.unitRegion) + logVol{W.scaleShift (point ε abc)}`.
* F5c/FrontierPointFinitenessClause:
  `∀ε>0 ∀abc, logVol{W.scaleShift (point ε abc)} < ⊤`.
* F5d/FrontierPointVolumeWeightClause:
  `∀ε>0 ∃D1, ∀abc, (logVol{W.scaleShift (point ε abc)}).toReal ≤
     (1+ε)·arithmeticWeight(abc) + D1`.
* P1/FrontierUnitMembershipClause: `∀ε>0 ∀abc, point ε abc ∈ W.unitRegion`.
* P2/FrontierPointHeightClause:
  `∀ε>0 ∀abc, (logVol{W.scaleShift (point ε abc)}).toReal ≤ logHeight₁(abc)`.

## Classification (green vs new quantitative input)

GREEN (conditional, from Geometry/StepXI bridge green):
* F5b FrontierSplitClause: `frontierSplitClause_of_unitMembership`
  (`ABCFrontierPointwisePremiseReduction.lean:84`) and value-realized
  `cor312GapSupply_sourceInterface_hsplit` (`Cor312ComparisonGapSupplyLayer.lean:127`);
* F5c FrontierPointFinitenessClause: `frontierPointFinitenessClause_of_unitMembership`
  (:95) and `cor312GapSupply_sourceInterface_hptfin` (:152);
* F5b/F5c from P1 also in `Cor312PointwiseMembershipWeakening.lean:111/...`.

PARTIAL (reduced to a dictionary/bound that is not proved):
* F5a FrontierUnitNormalizationClause: reduces to
  `ofReal D.degreeBound ≤ sourceHullVolume + ofReal D0`
  (`cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume`, :167);
  the normalization comparison is OPEN (SupplyLayer doc lines 29-39);
* F5d FrontierPointVolumeWeightClause: reduces to degree-weight dictionary
  `arithmeticWeight ≤ sourceLocalLogDegree` (`cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary`, :185);
  no source dictionary proved;
* P2 FrontierPointHeightClause: conditional source point-height dictionary
  (`cor312GapDict_sourcePointBound_of_degree_le_height` / `..._of_additiveBound`,
  `Cor312GapDictionaryLayer.lean:338/372`); no source dictionary yet;
* P1 FrontierUnitMembershipClause: satisfiable but NOT an interface theorem
  (`frontierUnitMembership_satisfiable` :212, `frontierUnitMembership_not_interface_theorem` :199);
  paper-faithful membership OPEN.

REFUTED AS STATED / NEED NEW QUANTITATIVE INPUT:
* F4a FrontierHeightWeightClause: `not_FrontierHeightWeightClause`
  (`ABCFrontierHeightWeightRefutation.lean:67`) — fails at (1,8,9) with ε=0.1;
  the clause needs an additive constant (corrected height-weight bound);
* F4b FrontierWeightRegionClause: calibration fails
  (`cor312Gap1_not_forall_arithmeticWeight_le_normalizedComparisonRegionVolume`,
  `Cor312ComparisonGapReduction.lean:272`); needs the valuation/degree dictionary and
  a corrected comparison region;
* F4 full FrontierHeightComparisonClause / F5 full FrontierRegionComparisonClause: OPEN
  paper links (IUT IV §2); conditional reductions only;
* reduced frontiers `ABCFrontierGapReduced`, `ABCFrontierPointwiseReduced` and
  `ABCFrontierPointwiseWeakened` are not inhabited / refuted on the calibration fixture
  (`not_ABCFrontierGapReduced` :75, `not_ABCFrontierPointwiseWeakened` :85,
  `abcFrontierPointwiseReduced_not_inhabited` :136).

Verdict: F5b/F5c are green conditional; F5a/F5d/P1/P2 are PARTIAL (named dictionary/bound);
F4a/F4b are refuted as stated and need corrected quantitative input; F4/F5 remain the open
paper comparison clauses.  ABC card NOT resolved.
No RETRACTED statement is used.  No sorry/axiom/True.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1FrontierQuantitativeActual

structure QuantRow where
  clause : String
  statement : String
  support : String
  status : String
  deriving Repr, DecidableEq

def quantRows : List QuantRow :=
  [ ⟨"F4 FrontierHeightComparisonClause", "forall eps>0 abc, logHeight1 <= (1+eps)*logVol(region point)", "OPEN paper link IUT IV sec.2; conditional Gap1 reductions only", "OPEN"⟩
  , ⟨"F5 FrontierRegionComparisonClause", "forall eps>0 exists D, logVol(region) <= (1+eps)*arithmeticWeight + logVol(hull) + D", "OPEN paper link; 5-input assembly conditional", "OPEN"⟩
  , ⟨"F4a FrontierHeightWeightClause", "forall eps>0 abc, logHeight1 <= (1+eps)*arithmeticWeight", "REFUTED at (1,8,9) eps=0.1 (not_FrontierHeightWeightClause)", "REFUTED_AS_STATED"⟩
  , ⟨"F4b FrontierWeightRegionClause", "forall eps>0 abc, arithmeticWeight <= logVol(region point)", "calibration refuted (cor312Gap1_not_forall...:272); needs degree dictionary + corrected region", "NEEDS_QUANT_INPUT"⟩
  , ⟨"F5a FrontierUnitNormalizationClause", "exists D0>=0, logVol(unit) <= logVol(hull)+ofReal D0", "reduces to degreeBound<=hullVolume (GapSupplyLayer:167); normalization comparison OPEN", "PARTIAL"⟩
  , ⟨"F5b FrontierSplitClause", "forall eps abc, logVol(region) <= logVol(scaleShift unit)+logVol{scaleShift point}", "GREEN conditional: frontierSplitClause_of_unitMembership (:84), sourceInterface_hsplit (:127)", "GREEN_CONDITIONAL"⟩
  , ⟨"F5c FrontierPointFinitenessClause", "forall eps abc, logVol{scaleShift point} < top", "GREEN conditional: frontierPointFinitenessClause_of_unitMembership (:95), sourceInterface_hptfin (:152)", "GREEN_CONDITIONAL"⟩
  , ⟨"F5d FrontierPointVolumeWeightClause", "forall eps exists D1, (logVol{scaleShift point}).toReal <= (1+eps)*arithmeticWeight + D1", "reduces to degree-weight dictionary (GapSupplyLayer:185); dictionary not proved", "PARTIAL"⟩
  , ⟨"P1 FrontierUnitMembershipClause", "forall eps abc, point eps abc in W.unitRegion", "satisfiable but not interface theorem (frontierUnitMembership_not_interface_theorem:199)", "PARTIAL"⟩
  , ⟨"P2 FrontierPointHeightClause", "forall eps abc, (logVol{scaleShift point}).toReal <= logHeight1", "conditional source point-height dictionary (GapDictLayer:338/372); missing", "PARTIAL"⟩
  , ⟨"reduced frontiers", "ABCFrontierGapReduced / PointwiseReduced / PointwiseWeakened", "not inhabited or refuted on calibration fixture", "REFUTED_ON_FIXTURE"⟩
  , ⟨"ABC card", "frontier => bridge interface => ABC", "conditional chain only; no frontier inhabitant", "NOT_RESOLVED"⟩
  ]

theorem quantRows_length : quantRows.length = 12 := rfl

theorem green_conditional_clauses :
    (quantRows.filter (fun r => r.status = "GREEN_CONDITIONAL")).length = 2 := by
  decide

theorem no_clause_discharged :
    (quantRows.filter (fun r => r.status = "DISCHARGED")).length = 0 := by
  decide

theorem abc_card_not_resolved :
    quantRows.any (fun r => r.status = "NOT_RESOLVED") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1FrontierQuantitativeActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1FrontierQuantitativeActual.green_conditional_clauses
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FrontierQuantitativeActual.abc_card_not_resolved
