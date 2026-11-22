import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge7Actual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1MeasureBridge8Actual — bounded step-set measure (real lemma)

Real Lean (no sorry/axiom): the P1 maximal degree of the paper's f0 step target for a
finite point set is bounded by max (maxDeg S) 1 after removing infinity bookkeeping.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge8Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge3Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge5Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge7Actual

attribute [local instance] Classical.decEq

universe u

/-- A finite image with infinity has P1 maximal degree max 1 (maxDeg S). -/
theorem maxDegP_insert_infty_image_le (S : Finset Qbar) :
    maxDegP (insert P1Point.infty (S.image (fun z => P1Point.ofFinite z))) <=
      max (maxDeg S) 1 := by
  rw [maxDegP_insert_infty_image]
  exact le_of_eq (max_comm 1 (maxDeg S))

/-- Row record. -/
def p1MeasureBridge8Rows : List (String × String) :=
  [ ("maxDegP_insert_infty_image_le", "PROVED") ]

theorem p1MeasureBridge8Rows_length : p1MeasureBridge8Rows.length = 1 := rfl

#check maxDegP_insert_infty_image_le

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge8Actual
end
