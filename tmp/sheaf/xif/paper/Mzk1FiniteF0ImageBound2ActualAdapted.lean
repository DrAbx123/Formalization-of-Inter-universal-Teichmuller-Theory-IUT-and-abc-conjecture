import tmp.sheaf.xif.paper.Mzk1FiniteF0ImageBoundActualAdapted

/-! # Mzk1FiniteF0ImageBound2ActualAdapted — f0 image bound corollaries (real)

Real Lean (no sorry/axiom): subset/union corollaries of the PROVED f0 image degree bound.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteF0ImageBound2ActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteF0ImageBoundActualAdapted

universe u

theorem maxDeg_f0Image_le_of_subset (S T : Finset Qbar) (alpha0 : Qbar) (h : S ⊆ T) :
    maxDeg (S.image (fun x => aeval x (minpoly ℚ alpha0))) <= maxDeg T :=
  le_trans (maxDeg_f0Image_le S alpha0) (maxDeg_mono h)

theorem maxDeg_f0Image_union_le (S T : Finset Qbar) (alpha0 : Qbar) :
    maxDeg ((S ∪ T).image (fun x => aeval x (minpoly ℚ alpha0))) <=
      max (maxDeg S) (maxDeg T) := by
  rw [maxDeg_union]
  exact maxDeg_f0Image_le (S ∪ T) alpha0

theorem maxDeg_f0Image_erase_le (S : Finset Qbar) (alpha0 : Qbar) (x : Qbar) :
    maxDeg ((S.erase x).image (fun y => aeval y (minpoly ℚ alpha0))) <= maxDeg S :=
  le_trans (maxDeg_f0Image_le (S.erase x) alpha0) (maxDeg_mono (Finset.erase_subset _ _))

def finiteF0ImageBound2Rows : List (String × String) :=
  [ ("maxDeg_f0Image_le_of_subset", "PROVED"),
    ("maxDeg_f0Image_union_le", "PROVED"),
    ("maxDeg_f0Image_erase_le", "PROVED") ]

theorem finiteF0ImageBound2Rows_length : finiteF0ImageBound2Rows.length = 3 := rfl

#check maxDeg_f0Image_le_of_subset

end LeanFormal.IUT.XiFPaper.Mzk1FiniteF0ImageBound2ActualAdapted
end
