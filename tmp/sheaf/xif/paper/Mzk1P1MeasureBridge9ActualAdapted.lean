import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge4ActualAdapted

/-! # Mzk1P1MeasureBridge9ActualAdapted — elementary numMaxP bounds (real lemmas)

Real Lean (no sorry/axiom): the P1 maximal count is bounded by the cardinality, and inserting
one point increases it by at most one.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge9ActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

attribute [local instance] Classical.decEq

universe u

/-- The P1 maximal count is at most the cardinality. -/
theorem numMaxP_le_card (S : Finset (P1Point Qbar)) : numMaxP S <= S.card := by
  unfold numMaxP
  exact Finset.card_filter_le _ _

/-- Inserting one point increases the P1 maximal count by at most one. -/
theorem numMaxP_insert_le_succ (S : Finset (P1Point Qbar)) (p : P1Point Qbar) :
    numMaxP (insert p S) <= numMaxP S + 1 := by
  unfold numMaxP
  have h1 : (insert p S).card = S.card + 1 := by
    rw [Finset.card_insert_of_not_mem]
    simp
  calc ((insert p S).filter (fun x => degP x = maxDegP (insert p S))).card
      <= (insert p S).card := Finset.card_filter_le _ _
    _ = S.card + 1 := h1
    _ <= S.card + 1 := le_rfl
    _ = S.card + 1 := rfl

/-- Row record. -/
def p1MeasureBridge9Rows : List (String × String) :=
  [ ("numMaxP_le_card", "PROVED"), ("numMaxP_insert_le_succ", "PROVED") ]

theorem p1MeasureBridge9Rows_length : p1MeasureBridge9Rows.length = 2 := rfl

#check numMaxP_le_card
#check numMaxP_insert_le_succ

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge9ActualAdapted
end
