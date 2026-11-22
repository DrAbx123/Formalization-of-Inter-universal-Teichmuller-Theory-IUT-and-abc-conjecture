import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge15Actual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1MeasureBridge16Actual — count laws for the P1 measure (real)

Real Lean (no sorry/axiom): idempotence and empty-set laws of the P1 maximal count.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge16Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge4Actual

attribute [local instance] Classical.decEq

universe u

theorem numMaxP_union_self (S : Finset (P1Point Qbar)) :
    numMaxP (S ∪ S) = numMaxP S := by
  rw [Finset.union_self]

theorem numMaxP_union_empty (S : Finset (P1Point Qbar)) :
    numMaxP (S ∪ ∅) = numMaxP S := by
  rw [Finset.union_empty]

theorem numMaxP_insert_infty_image_numMax (S : Finset Qbar) (h2 : 2 <= maxDeg S) :
    numMaxP (insert P1Point.infty (S.image (fun z => P1Point.ofFinite z))) = numMaxP (S.image (fun z => P1Point.ofFinite z)) := by
  have himg : numMaxP (S.image (fun z => P1Point.ofFinite z)) = numMax S := numMaxP_image_ofFinite S
  rw [himg]
  exact numMaxP_insert_infty_image S h2

def p1MeasureBridge16Rows : List (String × String) :=
  [ ("numMaxP_union_self", "PROVED"), ("numMaxP_union_empty", "PROVED"),
    ("numMaxP_insert_infty_image_numMax", "PROVED (reuse)") ]

theorem p1MeasureBridge16Rows_length : p1MeasureBridge16Rows.length = 3 := rfl

#check numMaxP_union_self

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge16Actual
end
