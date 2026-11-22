import tmp.sheaf.xif.paper.Mzk1FiniteMeasureLawsActualAdapted

/-! # Mzk1FiniteMeasureUnionCardActualAdapted — union cardinality bounds (real)

Real Lean (no sorry/axiom): cardinality bounds for the finite maximal count of unions and
insertions.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureUnionCardActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActualAdapted

attribute [local instance] Classical.decEq

universe u

theorem numMax_union_le_card (S T : Finset Qbar) :
    numMax (S ∪ T) <= (S ∪ T).card :=
  numMax_le_card _

theorem numMax_insert_le_card (S : Finset Qbar) (x : Qbar) :
    numMax (insert x S) <= (insert x S).card :=
  numMax_le_card _

def finiteMeasureUnionCardRows : List (String × String) :=
  [ ("numMax_union_le_card", "PROVED"), ("numMax_insert_le_card", "PROVED") ]

theorem finiteMeasureUnionCardRows_length : finiteMeasureUnionCardRows.length = 2 := rfl

#check numMax_union_le_card

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureUnionCardActualAdapted
end
