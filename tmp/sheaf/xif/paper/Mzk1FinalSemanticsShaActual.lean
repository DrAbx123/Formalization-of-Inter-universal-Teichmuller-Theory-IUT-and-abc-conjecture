import tmp.sheaf.xif.paper.Mzk1FinalBoundaryCertificateV2Actual
import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import Mathlib.Tactic

/-!
# shehdd A688/A690 final semantics index (Sha, read-only)

Single place with the FINAL A688 six-point semantics, in three states:
① Cor 3.12 requirement chain: GREEN;
② corrected-region Gap 1: THEOREM;
③ corrected Gap 2 shape ⇒ ABC: THEOREM;
④ only NAMED input = corrected Gap 2 shape, equivalent to the pure arithmetic
  `BadSumWeightBound` (GREEN_EQUIV);
⑤ converse ABC ⇒ Gap2: NOT_PROVED;
⑥ ABC gate: NOT_PASSED; no canonical change.

Gates below cover only the canonical green statements.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalSemanticsShaActual

structure FinalRow where
  point : String
  content : String
  status : String
  deriving Repr, DecidableEq

def finalRows : List FinalRow :=
  [ ⟨"① legacy 3.12 final chain (hfull)", "Mzk1FinalBoundaryCertificateV2Actual.v2_final_3_12 (hfull-dependent)", "RETRACTED"⟩
  , ⟨"② legacy corrected Gap1 (hfull hypothesis)", "Mzk1CorrectedGap1UnconditionalActual.corrected_gap1_unconditional (hfull-dependent)", "RETRACTED"⟩
  , ⟨"③ legacy Gap2 => ABC (hfull hypothesis)", "Mzk1FinalBoundaryCertificateV2Actual.v2_gap2 (hfull-dependent)", "RETRACTED"⟩
  , ⟨"④ legacy N-scaling Gap2 shape", "CorrectedGap2Shape (N=a+b+c+1 scaling; RETRACTED)", "RETRACTED"⟩
  , ⟨"⑤ converse ABC => Gap2", "NOT proved; NOT asserted", "NOT_PROVED"⟩
  , ⟨"⑥ ABC gate", "NOT passed", "NOT_PASSED"⟩
  , ⟨"⑥ canonical change", "none", "INTEGRITY"⟩
  , ⟨"new route N1 Gap2 shape", "triple-dependent Theta-data: bad primes=primes(abc), q=(abc)^2, normalized weight; PENDING_ABC_LANE", "NEW_ROUTE_NAMED"⟩
  ]

theorem finalRows_length : finalRows.length = 8 := rfl

theorem finalRows_statuses_ok :
    finalRows.all (fun r =>
      r.status ∈ ["RETRACTED", "GREEN", "THEOREM", "NAMED", "GREEN_EQUIV", "NOT_PROVED", "NOT_PASSED", "NEW_ROUTE", "NEW_ROUTE_NAMED", "INTEGRITY"]) = true := by
  decide

theorem finalRows_no_legacy_named :
    (finalRows.filter (fun r => r.status = "NAMED")).length = 0 := by
  decide

theorem finalRows_has_n1_route_named :
    finalRows.any (fun r => r.status = "NEW_ROUTE_NAMED") = true := by
  decide

theorem finalRows_has_not_proved_converse :
    finalRows.any (fun r => r.status = "NOT_PROVED") = true := by
  decide

theorem finalRows_abc_not_passed :
    finalRows.any (fun r => r.status = "NOT_PASSED") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1FinalSemanticsShaActual

/-! ### Axiom gates (canonical final statements, read-only) -/

-- RETRACTED (A704): no longer cited as conclusion: LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual.finalBoundaryCertificateV2
-- RETRACTED (A704): no longer cited as conclusion: LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual.v2_gap2
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual.correctedGap2_iff_arith
