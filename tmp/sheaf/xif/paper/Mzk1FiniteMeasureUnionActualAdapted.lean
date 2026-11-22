import tmp.sheaf.xif.paper.Mzk1FiniteMeasureLawsActualAdapted

/-! # Mzk1FiniteMeasureUnionActualAdapted — finite numMax union bound (real)

Real Lean (no sorry/axiom): when both parts share the maximal degree, the finite maximal
count of the union is subadditive.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureUnionActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActualAdapted

attribute [local instance] Classical.decEq

universe u

theorem numMax_union_le_of_maxDeg_eq (S T : Finset Qbar)
    (h : maxDeg S = maxDeg T) :
    numMax (S ∪ T) <= numMax S + numMax T := by
  unfold numMax
  rw [maxDeg_union, h, max_self, Finset.filter_union]
  exact Finset.card_union_le _ _

def finiteMeasureUnionRows : List (String × String) :=
  [ ("numMax_union_le_of_maxDeg_eq", "PROVED") ]

theorem finiteMeasureUnionRows_length : finiteMeasureUnionRows.length = 1 := rfl

#check numMax_union_le_of_maxDeg_eq

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureUnionActualAdapted
end
