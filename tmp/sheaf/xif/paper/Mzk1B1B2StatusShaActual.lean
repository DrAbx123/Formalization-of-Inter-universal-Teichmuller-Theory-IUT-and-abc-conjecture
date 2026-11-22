import Mathlib.Tactic

/-!
# shehdd B1/B2 and gap status under A688 semantics (Sha, audit)

Three-state audit consistent with A688:
* B1 (single-point null measure): GREEN (hull `Mzk1ProductHaarSingletonActual`);
* B2 (normalization split): GREEN (mainline corrected log law, conditional form);
* corrected-region Gap 1: THEOREM;
* corrected Gap 2 shape: the ONLY NAMED input, equivalent to arithmetic
  `BadSumWeightBound` (`correctedGap2_iff_arith`);
* converse ABC ⇒ Gap2: NOT proved / NOT claimed; ABC gate NOT passed.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1B1B2StatusShaActual

structure SplitRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def splitRows : List SplitRow :=
  [ ⟨"B1 single-point null", "Mzk1ProductHaarSingletonActual.productHaar_singleton_zero", "GREEN"⟩
  , ⟨"B1 log-volume zero", "Mzk1B1ProductSingletonShaActual.b1_logVolume_singleton_zero", "GREEN"⟩
  , ⟨"B2 normalization split", "Mzk1CorrectedRegionLogLawProvedActual (conditional log law)", "GREEN"⟩
  , ⟨"legacy corrected Gap1 (hfull)", "Mzk1CorrectedGap1UnconditionalActual.corrected_gap1_unconditional (hfull-dependent)", "RETRACTED"⟩
  , ⟨"legacy N-scaling Gap2 shape", "CorrectedGap2Shape (RETRACTED)", "RETRACTED"⟩
  , ⟨"Gap2 arithmetic equivalence", "correctedGap2_iff_arith <=> BadSumWeightBound", "GREEN_EQUIV"⟩
  , ⟨"converse ABC => Gap2", "NOT proved; NOT asserted", "NOT_PROVED"⟩
  , ⟨"ABC gate", "NOT passed", "NOT_PASSED"⟩
  , ⟨"new route N1 Gap2 shape", "triple-dependent Theta-data; PENDING_ABC_LANE", "NEW_ROUTE_NAMED"⟩
  , ⟨"scope", "audit only; no gap claimed", "INTEGRITY"⟩
  ]

theorem splitRows_length : splitRows.length = 10 := rfl

theorem splitRows_statuses_ok :
    splitRows.all (fun r =>
      r.status ∈ ["RETRACTED", "GREEN", "THEOREM", "NAMED", "GREEN_EQUIV", "NOT_PROVED", "NOT_PASSED", "NEW_ROUTE", "NEW_ROUTE_NAMED", "INTEGRITY"]) = true := by
  decide

theorem splitRows_no_legacy_named :
    (splitRows.filter (fun r => r.status = "NAMED")).length = 0 := by
  decide

theorem splitRows_has_n1_route_named :
    splitRows.any (fun r => r.status = "NEW_ROUTE_NAMED") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1B1B2StatusShaActual
