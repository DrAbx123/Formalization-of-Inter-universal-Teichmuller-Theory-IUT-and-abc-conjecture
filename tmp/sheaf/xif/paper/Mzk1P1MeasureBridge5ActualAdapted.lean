import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge3ActualAdapted

/-! # Mzk1P1MeasureBridge5ActualAdapted — maxDegP corollaries for step images

Real Lean (no sorry/axiom): maxDegP of images of finite sets under ofFinite, union with
infinity, and the corresponding bound by maxDeg of the finite part.  Registry 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge5ActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge3ActualAdapted

attribute [local instance] Classical.decEq

universe u

/-- P1 maximal degree of the finite image is the finite maxDeg. -/
theorem maxDegP_image_ofFinite (S : Finset Qbar) :
    maxDegP (S.image (fun z => P1Point.ofFinite z)) = maxDeg S :=
  Mzk1NestedInductionActual.maxDegP_image_ofFinite S

/-- P1 maximal degree of the finite image plus infinity is max 1 maxDeg. -/
theorem maxDegP_insert_infty_image (S : Finset Qbar) :
    maxDegP (insert P1Point.infty (S.image (fun z => P1Point.ofFinite z))) =
      max 1 (maxDeg S) := by
  rw [maxDegP_insert, maxDegP_image_ofFinite]
  rfl

/-- The finite image P1 degree is bounded by the insert-infinity closure. -/
theorem maxDegP_image_le_insert_infty (S : Finset Qbar) :
    maxDegP (S.image (fun z => P1Point.ofFinite z)) <=
      maxDegP (insert P1Point.infty (S.image (fun z => P1Point.ofFinite z))) :=
  maxDegP_mono (Finset.subset_insert _ _)

/-- Row record. -/
def p1MeasureBridge5Rows : List (String × String) :=
  [ ("maxDegP_image_ofFinite", "PROVED"), ("maxDegP_insert_infty_image", "PROVED"),
    ("maxDegP_image_le_insert_infty", "PROVED") ]

theorem p1MeasureBridge5Rows_length : p1MeasureBridge5Rows.length = 3 := rfl

#check maxDegP_insert_infty_image

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge5ActualAdapted
end
