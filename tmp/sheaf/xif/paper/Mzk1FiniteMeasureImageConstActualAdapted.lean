import tmp.sheaf.xif.paper.Mzk1FiniteMeasureLawsActualAdapted
import tmp.sheaf.xif.paper.Mzk1FiniteMeasureDegenerateActualAdapted

/-! # Mzk1FiniteMeasureImageConstActualAdapted — constant image value (real)

Real Lean (no sorry/axiom): the finite maximal degree of a constant image is the degree of
the constant.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImageConstActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureDegenerateActualAdapted

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_image_const (S : Finset Qbar) (x : Qbar) (hS : S.Nonempty) :
    maxDeg (S.image (fun _ => x)) = degQ x := by
  rw [Finset.image_const]
  exact maxDeg_singleton x

theorem numMax_image_const (S : Finset Qbar) (x : Qbar) (hS : S.Nonempty) :
    numMax (S.image (fun _ => x)) = numMax {x} := by
  rw [Finset.image_const]

def finiteMeasureImageConstRows : List (String × String) :=
  [ ("maxDeg_image_const", "PROVED"), ("numMax_image_const", "PROVED") ]

theorem finiteMeasureImageConstRows_length : finiteMeasureImageConstRows.length = 2 := rfl

#check maxDeg_image_const

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImageConstActualAdapted
end
