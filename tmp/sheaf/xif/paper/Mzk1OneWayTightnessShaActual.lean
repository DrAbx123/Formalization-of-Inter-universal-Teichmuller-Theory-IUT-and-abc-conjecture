import tmp.sheaf.xif.paper.Mzk1FinalBoundaryCertificateV2Actual
import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import Mathlib.Tactic

/-!
# shehdd A689 one-way tightness of the corrected Gap2 boundary (Sha, read-only)

One-way tightness statement consistent with A688:
* corrected Gap2 shape ⇒ `ABCConjecture` is a THEOREM (canonical V2 `v2_gap2`);
* corrected Gap2 shape ⇔ pure arithmetic `BadSumWeightBound`
  (`correctedGap2_iff_arith`) — so the boundary's strength is exactly that of the
  arithmetic BadSumWeightBound;
* the converse `ABCConjecture` ⇒ corrected Gap2 shape is NOT proved and NOT
  asserted, hence the tightness is ONE-WAY;
* ABC gate NOT passed; no canonical change.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1OneWayTightnessShaActual

structure OneWayRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def oneWayRows : List OneWayRow :=
  [ ⟨"legacy Gap2 => ABC (hfull)", "canonical V2 v2_gap2 (hfull-dependent)", "RETRACTED"⟩
  , ⟨"legacy Gap2 shape <=> arithmetic", "correctedGap2_iff_arith <=> BadSumWeightBound (N-scaling; RETRACTED route)", "RETRACTED"⟩
  , ⟨"ABC => Gap2 shape", "NOT proved; NOT asserted", "NOT_PROVED"⟩
  , ⟨"tightness direction", "one-way: boundary strength = BadSumWeightBound strength", "ONE_WAY"⟩
  , ⟨"ABC gate", "NOT passed", "NOT_PASSED"⟩
  , ⟨"canonical change", "none", "INTEGRITY"⟩
  , ⟨"new route N1 Gap2 shape", "triple-dependent Theta-data; PENDING_ABC_LANE", "NEW_ROUTE_NAMED"⟩
  ]

theorem oneWayRows_length : oneWayRows.length = 7 := rfl

theorem oneWayRows_statuses_ok :
    oneWayRows.all (fun r =>
      r.status ∈ ["RETRACTED", "THEOREM", "GREEN_EQUIV", "NOT_PROVED", "ONE_WAY", "NOT_PASSED", "NEW_ROUTE", "NEW_ROUTE_NAMED", "INTEGRITY"]) = true := by
  decide

theorem oneWay_has_no_converse :
    oneWayRows.any (fun r => r.item = "ABC => Gap2 shape" ∧ r.status = "NOT_PROVED") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1OneWayTightnessShaActual

/-! ### Axiom gates (canonical one-way direction, read-only) -/

-- RETRACTED (A704): no longer cited as conclusion: LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual.v2_gap2
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual.correctedGap2_iff_arith
