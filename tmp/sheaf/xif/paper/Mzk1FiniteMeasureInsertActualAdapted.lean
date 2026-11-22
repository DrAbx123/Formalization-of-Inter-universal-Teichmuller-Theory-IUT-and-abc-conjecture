import tmp.sheaf.xif.paper.Mzk1FiniteMeasureLawsActualAdapted

/-! # Mzk1FiniteMeasureInsertActualAdapted — finite numMax insertion law (real)

Real Lean (no sorry/axiom): inserting a point strictly below the finite maximal degree does
not change the finite maximal count.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureInsertActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActualAdapted

attribute [local instance] Classical.decEq

universe u

theorem numMax_insert_eq_of_deg_lt (S : Finset Qbar) (x : Qbar)
    (h : degQ x < maxDeg S) :
    numMax (insert x S) = numMax S := by
  unfold numMax
  have hmax : maxDeg (insert x S) = maxDeg S := by
    rw [maxDeg_insert, max_eq_left (le_of_lt h)]
  rw [hmax, Finset.filter_insert]
  rw [if_neg (ne_of_lt h)]

def finiteMeasureInsertRows : List (String × String) :=
  [ ("numMax_insert_eq_of_deg_lt", "PROVED") ]

theorem finiteMeasureInsertRows_length : finiteMeasureInsertRows.length = 1 := rfl

#check numMax_insert_eq_of_deg_lt

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureInsertActualAdapted
end
