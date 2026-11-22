import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge3ActualAdapted

/-! # Mzk1P1MeasureBridge6ActualAdapted — maxDegP subset/erase laws (real lemmas)

Real Lean (no sorry/axiom): monotonicity corollaries of the P1 maximal-degree measure for
Finset subset, erase, diff and intersection, used when bounding the concrete f0 step target.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge6ActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge3ActualAdapted

attribute [local instance] Classical.decEq

universe u

/-- Subset: the P1 maximal degree of S is bounded by that of T. -/
theorem maxDegP_le_of_subset {S T : Finset (P1Point Qbar)} (h : S ⊆ T) :
    maxDegP S <= maxDegP T := maxDegP_mono h

/-- Erasing a point cannot increase the P1 maximal degree. -/
theorem maxDegP_erase_le (S : Finset (P1Point Qbar)) (p : P1Point Qbar) :
    maxDegP (S.erase p) <= maxDegP S := maxDegP_mono (Finset.erase_subset _ _)

/-- Removing a set cannot increase the P1 maximal degree. -/
theorem maxDegP_diff_le (S T : Finset (P1Point Qbar)) :
    maxDegP (S \ T) <= maxDegP S := maxDegP_mono (Finset.diff_subset _ _)

/-- Intersecting cannot increase the P1 maximal degree. -/
theorem maxDegP_inter_le (S T : Finset (P1Point Qbar)) :
    maxDegP (S ∩ T) <= maxDegP S := maxDegP_mono (Finset.inter_subset_left _ _)

/-- Row record. -/
def p1MeasureBridge6Rows : List (String × String) :=
  [ ("maxDegP_le_of_subset", "PROVED"), ("maxDegP_erase_le", "PROVED"),
    ("maxDegP_diff_le", "PROVED"), ("maxDegP_inter_le", "PROVED") ]

theorem p1MeasureBridge6Rows_length : p1MeasureBridge6Rows.length = 4 := rfl

#check maxDegP_le_of_subset
#check maxDegP_erase_le

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge6ActualAdapted
end
