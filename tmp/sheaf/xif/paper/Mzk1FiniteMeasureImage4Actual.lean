import tmp.sheaf.xif.paper.Mzk1FiniteMeasureLawsActual

/-! # Mzk1FiniteMeasureImage4Actual — identity image laws (real)

Real Lean (no sorry/axiom): the finite measure is invariant under the identity map.  Registry
frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImage4Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_image_id (S : Finset Qbar) : maxDeg (S.image id) = maxDeg S := by
  rw [Finset.image_id]

theorem numMax_image_id (S : Finset Qbar) : numMax (S.image id) = numMax S := by
  rw [Finset.image_id]

def finiteMeasureImage4Rows : List (String × String) :=
  [ ("maxDeg_image_id", "PROVED"), ("numMax_image_id", "PROVED") ]

theorem finiteMeasureImage4Rows_length : finiteMeasureImage4Rows.length = 2 := rfl

#check maxDeg_image_id

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImage4Actual
end
