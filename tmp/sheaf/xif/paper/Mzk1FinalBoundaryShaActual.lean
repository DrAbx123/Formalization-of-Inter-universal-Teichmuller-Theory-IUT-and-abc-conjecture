import tmp.sheaf.xif.paper.Mzk1PaperRegionNecessityFinalActual
import tmp.sheaf.xif.paper.Mzk1S1902BridgeInterfaceActual
import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import tmp.sheaf.xif.paper.Mzk1GapTightnessShaActual
import tmp.sheaf.xif.paper.Mzk1GapStructuralShapeAuditShaActual
import Mathlib.Tactic

/-!
# shehdd A648 FinalBoundary audit (Sha, read-only)

Final boundary summary: what is GREEN vs what remains NAMED, with read-only axiom
gates for the canonical final statements.

* GREEN: canonical concrete bridge `s1902Bridge_abc`, triple-dependent
  `abc_of_tripleComparison`, paper-region-necessity final audit
  (`paperRegionNecessityFinal`, `abc_of_gapProps`), A618 obstruction, hqneg
  discharged, gap tightness calibration;
* NAMED and NOT claimed proved: Gap 1 (`height_le_normalizedRegionVolume`) and
  Gap 2 (`regionVolume_le_normalizedWeight`) — the two IUT IV Thm 1.10 inputs;
* scope: conditional ABC only; ABC gate NOT passed.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryShaActual

structure BoundaryRow where
  component : String
  status : String
  note : String
  deriving Repr, DecidableEq

def boundaryRows : List BoundaryRow :=
  [ ⟨"canonical S1902 bridge", "GREEN", "Mzk1S1902BridgeInterfaceActual.s1902Bridge_abc (gate trio)"⟩
  , ⟨"triple-dependent ABC", "GREEN", "Mzk1PaperComparisonRegionScalingActual.abc_of_tripleComparison (gate trio)"⟩
  , ⟨"paper region necessity final", "GREEN", "paperRegionNecessityFinal / abc_of_gapProps (gates trio)"⟩
  , ⟨"A618 obstruction", "GREEN", "Mzk1A618ScalingObstructionActual.identity_scaleShift_obstruction (gate trio)"⟩
  , ⟨"hqneg discharged", "GREEN", "Mzk1Cor312HqnegDischargedActual.cor312_hqneg_discharged (gate trio)"⟩
  , ⟨"gap tightness calibration", "GREEN", "Mzk1GapTightnessShaActual (slack witnesses + recovery iff)"⟩
  , ⟨"Gap 1", "NAMED", "height_le_normalizedRegionVolume (IUT IV Thm 1.10)"⟩
  , ⟨"Gap 2", "NAMED", "regionVolume_le_normalizedWeight (IUT IV Thm 1.10)"⟩
  , ⟨"ABC gate", "CONDITIONAL", "two estimates / gaps are explicit hypotheses; NOT passed"⟩
  ]

theorem boundaryRows_length : boundaryRows.length = 9 := rfl

theorem boundaryRows_statuses_ok :
    boundaryRows.all (fun r =>
      r.status ∈ ["GREEN", "NAMED", "CONDITIONAL"]) = true := by
  decide

theorem boundary_has_gap1 :
    boundaryRows.any (fun r => r.component = "Gap 1") = true := by
  decide

theorem boundary_has_gap2 :
    boundaryRows.any (fun r => r.component = "Gap 2") = true := by
  decide

theorem boundary_has_conditional_gate :
    boundaryRows.any (fun r => r.status = "CONDITIONAL") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryShaActual

/-! ### Read-only axiom gates of the canonical final statements -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperRegionNecessityFinalActual.paperRegionNecessityFinal
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperRegionNecessityFinalActual.abc_of_gapProps
#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1902BridgeInterfaceActual.s1902Bridge_abc
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual.abc_of_tripleComparison
