import tmp.sheaf.xif.paper.Mzk1FiniteMeasureLawsActual

/-! # Mzk1FiniteMeasureEraseActual — erase/insert bounds (real)

Real Lean (no sorry/axiom): erasing and re-inserting a point gives a set whose maximal degree
is bounded by the inserted set.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureEraseActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_erase_le_insert (S : Finset Qbar) (x : Qbar) :
    maxDeg (S.erase x) <= maxDeg (insert x S) :=
  maxDeg_mono (le_trans (Finset.erase_subset _ _) (Finset.subset_insert _ _))

theorem maxDeg_insert_erase_le_insert (S : Finset Qbar) (x : Qbar) :
    maxDeg (insert x (S.erase x)) <= maxDeg (insert x S) :=
  maxDeg_mono (Finset.insert_subset_insert x (Finset.erase_subset _ _))

def finiteMeasureEraseRows : List (String × String) :=
  [ ("maxDeg_erase_le_insert", "PROVED"), ("maxDeg_insert_erase_le_insert", "PROVED") ]

theorem finiteMeasureEraseRows_length : finiteMeasureEraseRows.length = 2 := rfl

#check maxDeg_erase_le_insert

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureEraseActual
end
