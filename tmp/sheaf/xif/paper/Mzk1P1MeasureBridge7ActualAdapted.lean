import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge5ActualAdapted

/-! # Mzk1P1MeasureBridge7ActualAdapted — maxDegP of finite image unions (real lemmas)

Real Lean (no sorry/axiom): P1 maximal degree of a union with a finite image, and of a union
of two finite images.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge7ActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge3Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge5ActualAdapted

attribute [local instance] Classical.decEq

universe u

/-- P1 maximal degree of a union with a finite image. -/
theorem maxDegP_union_image (S : Finset Qbar) (T : Finset (P1Point Qbar)) :
    maxDegP ((S.image (fun z => P1Point.ofFinite z)) ∪ T) =
      max (maxDeg S) (maxDegP T) := by
  rw [maxDegP_union, maxDegP_image_ofFinite]

/-- P1 maximal degree of a union of two finite images. -/
theorem maxDegP_union_images (S T : Finset Qbar) :
    maxDegP ((S.image (fun z => P1Point.ofFinite z)) ∪
        (T.image (fun z => P1Point.ofFinite z))) =
      max (maxDeg S) (maxDeg T) := by
  rw [maxDegP_union, maxDegP_image_ofFinite, maxDegP_image_ofFinite]

/-- Row record. -/
def p1MeasureBridge7Rows : List (String × String) :=
  [ ("maxDegP_union_image", "PROVED"), ("maxDegP_union_images", "PROVED") ]

theorem p1MeasureBridge7Rows_length : p1MeasureBridge7Rows.length = 2 := rfl

#check maxDegP_union_image
#check maxDegP_union_images

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge7ActualAdapted
end
