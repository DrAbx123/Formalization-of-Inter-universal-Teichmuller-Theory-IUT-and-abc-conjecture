import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge9ActualAdapted

/-! # Mzk1P1MeasureBridge12ActualAdapted — safe measure corollaries (real lemmas)

Real Lean (no sorry/axiom): immediate corollaries of the elementary P1 measure bounds,
reusable when bounding concrete step targets.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge12ActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge3Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge9ActualAdapted

attribute [local instance] Classical.decEq

universe u

/-- The P1 maximal count of a subset is at most the ambient cardinality. -/
theorem numMaxP_le_card_of_subset {S T : Finset (P1Point Qbar)} (h : S ⊆ T) :
    numMaxP S <= T.card := by
  have h1 : numMaxP S <= S.card := numMaxP_le_card S
  have h2 : S.card <= T.card := Finset.card_le_card h
  omega

/-- Singleton maximal degree is the degree of the point. -/
theorem maxDegP_singleton (p : P1Point Qbar) : maxDegP {p} = degP p := by
  unfold maxDegP
  rw [Finset.sup_singleton]

/-- Inserting a point has P1 maximal degree at most the old maximum plus the new degree. -/
theorem maxDegP_insert_le (S : Finset (P1Point Qbar)) (p : P1Point Qbar) :
    maxDegP (insert p S) <= degP p + maxDegP S := by
  unfold maxDegP
  rw [Finset.sup_insert]
  exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

def p1MeasureBridge12Rows : List (String × String) :=
  [ ("numMaxP_le_card_of_subset", "PROVED"), ("maxDegP_singleton", "PROVED"),
    ("maxDegP_insert_le", "PROVED") ]

theorem p1MeasureBridge12Rows_length : p1MeasureBridge12Rows.length = 3 := rfl

#check numMaxP_le_card_of_subset
#check maxDegP_singleton

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge12ActualAdapted
end
