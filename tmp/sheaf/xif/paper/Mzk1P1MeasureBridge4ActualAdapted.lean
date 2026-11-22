import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge3ActualAdapted

/-! # Mzk1P1MeasureBridge4ActualAdapted — numMaxP Finset laws (real lemmas, corrected statement)

Real Lean (no sorry/axiom): the P1 maximal count is additive over unions when both parts
share the same maximal degree, and inserting a point strictly below the maximal degree does
not change the count.  These are the counting ingredients of the P1 measure transfer.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge4ActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge3ActualAdapted

attribute [local instance] Classical.decEq

universe u

/-- When both parts share the maximal degree, the P1 maximal count of the union is
subadditive. -/
theorem numMaxP_union_le_of_maxDegP_eq (S T : Finset (P1Point Qbar))
    (h : maxDegP S = maxDegP T) :
    numMaxP (S ∪ T) <= numMaxP S + numMaxP T := by
  unfold numMaxP
  rw [maxDegP_union, h, max_self]
  rw [Finset.filter_union]
  exact Finset.card_union_le _ _

/-- Inserting a point strictly below the maximal degree does not change the count. -/
theorem numMaxP_insert_eq_of_deg_lt (S : Finset (P1Point Qbar)) (p : P1Point Qbar)
    (hp : degP p < maxDegP S) :
    numMaxP (insert p S) = numMaxP S := by
  unfold numMaxP
  have hmax : maxDegP (insert p S) = maxDegP S := by
    rw [maxDegP_insert, max_eq_left (le_of_lt hp)]
  rw [hmax, Finset.filter_insert]
  rw [if_neg (ne_of_lt hp)]

/-- Row record. -/
def p1MeasureBridge4Rows : List (String × String) :=
  [ ("numMaxP_union_le_of_maxDegP_eq", "PROVED"),
    ("numMaxP_insert_eq_of_deg_lt", "PROVED") ]

theorem p1MeasureBridge4Rows_length : p1MeasureBridge4Rows.length = 2 := rfl

#check numMaxP_union_le_of_maxDegP_eq
#check numMaxP_insert_eq_of_deg_lt

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge4ActualAdapted
end
