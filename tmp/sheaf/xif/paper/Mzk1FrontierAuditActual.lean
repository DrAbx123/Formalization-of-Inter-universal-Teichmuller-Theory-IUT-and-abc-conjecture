import Mathlib.Tactic

/-!
# A839 ABCFrontier / gap-supply audit (shehdd)

Read: `LeanFormal/IUT/ABCBridge/Bridge/ABCFrontier.lean`,
`ABCFrontierReductions.lean`, `ABCFrontierPointwisePremiseReduction.lean`,
`ABCFrontierHeightWeightRefutation.lean`, `Cor312ComparisonGapReduction.lean`,
`Cor312ComparisonGapSupplyLayer.lean`, `Cor312ToABCBridgeInterface.lean`.

## Frontier fields (Cor312ToABCBridgeInterface:404-412)
* `carrier : Type u` (F1, data);
* `hullData : IQHullLogVolumeInterface carrier` (F2, interface data);
* `epsilonComparison : ∀ eps>0, Cor312EpsilonArithmeticComparison hullData eps`
  (the arithmetic content: F4 height comparison + F5 volume/weight comparison).

## Status
* F1/F2/F3a: DATA clauses; fixture supplies are green (`Cor312ToABCBridgeInterface.lean`
  fixtures) but paper-faithful carrier/hull/point are OPEN (ABCFrontier doc, honest boundary).
* F4 gap 1: OPEN paper link (IUT IV §2); only conditional reductions
  (`cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound`, :198; additive :557;
  singleton :502).  The calibration carrier refutes the weight comparison
  (`cor312Gap1_not_forall_arithmeticWeight_le_normalizedComparisonRegionVolume`, :272).
* F5 gap 2: OPEN (IUT IV §2 main estimate); reduced to five named inputs
  hunit/hsplit/hptfin/hweightvol/hpoint (`cor312GapAssembly_epsilonComparisonOfReducedInputs`,
  Cor312ComparisonGapReduction.lean:367).
* `Cor312ComparisonGapSupplyLayer`: does NOT fill any gap field.  It supplies `hsplit` and
  `hptfin` for the value-realized interface (conditional on `SourceUnitRegionHaarData`),
  leaves `hunit`, `hweightvol`, `hpoint` open/gap (module doc lines 29-57;
  `cor312ComparisonGapReductionObligation` note: 'NOT proved: any of the five named inputs').
* Reduced frontiers: `ABCFrontier.reduce_gapReductionInputs`,
  `ABCFrontier.reduce_pointwiseResidual` are sufficient factorizations, not constructed
  supplies; the calibration fixture does not inhabit them
  (`not_ABCFrontierGapReduced`, `not_ABCFrontierPointwiseWeakened`,
  `not_FrontierHeightWeightClause`); `abcFrontierPointwiseReduced_not_inhabited`.
* `Nonempty Cor312ToABCBridgeInterface` is equivalent to `ABCConjecture`
  (`cor312ToABCBridgeInterface_nonempty_iff_abcConjecture`, :605): it is NOT supplied;
  ABC is not proved.
* Our `Mzk1ABCTwoEstimates` is a different object (height/volume estimates over all
  triples); no Lean equivalence with the frontier/gap layer exists (PENDING dictionary).

Verdict: the gap supply is NOT constructed; the frontier is exactly the two comparison
clauses F4/F5 plus paper-faithful data F1/F2/F3a, all open.  ABC card NOT resolved.
No RETRACTED statement is used.  No sorry/axiom/True.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1FrontierAuditActual

structure FrontierRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def frontierRows : List FrontierRow :=
  [ ⟨"F1 carrier (interface field)", "Type u data; fixture supplies green; paper-faithful carrier OPEN", "DATA_FIXTURE"⟩
  , ⟨"F2 hullData (interface field)", "IQHullLogVolumeInterface data; fixture supplies green; paper hull OPEN", "DATA_FIXTURE"⟩
  , ⟨"F3a logShellPoint", "named point datum; fixture Real.log c; paper point OPEN", "DATA_FIXTURE"⟩
  , ⟨"F4 gap 1 (height comparison)", "OPEN paper link IUT IV sec.2; conditional reductions only (GapReduction:198/:557)", "OPEN"⟩
  , ⟨"F5 gap 2 (volume/weight comparison)", "OPEN; reduced to hunit/hsplit/hptfin/hweightvol/hpoint", "OPEN"⟩
  , ⟨"GapSupplyLayer", "hsplit+hptfin supplied conditionally (SourceUnitRegionHaarData); hunit/hweightvol/hpoint missing; NO gap field filled", "PARTIAL"⟩
  , ⟨"reduced frontiers", "sufficient factorizations; calibration refutes them (not_ABCFrontierGapReduced etc.)", "REFUTED_ON_FIXTURE"⟩
  , ⟨"Nonempty Cor312ToABCBridgeInterface", "equivalent to ABCConjecture (:605); not supplied", "MISSING"⟩
  , ⟨"our ABCTwoEstimates", "height/volume estimates object; no Lean bridge/equivalence to frontier", "DIFFERENT_OBJECT"⟩
  , ⟨"ABC card", "NOT resolved; F4/F5 + paper data open", "NOT_RESOLVED"⟩
  ]

theorem frontierRows_length : frontierRows.length = 10 := rfl

theorem no_frontier_field_discharged :
    (frontierRows.filter (fun r => r.status = "DISCHARGED")).length = 0 := by
  decide

theorem frontier_gap_open :
    frontierRows.any (fun r => r.status = "OPEN") = true := by
  decide

theorem abc_card_not_resolved :
    frontierRows.any (fun r => r.status = "NOT_RESOLVED") = true := by
  decide

theorem missing_frontier_premises :
    frontierRows.any (fun r => r.status = "MISSING") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1FrontierAuditActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1FrontierAuditActual.no_frontier_field_discharged
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FrontierAuditActual.abc_card_not_resolved
