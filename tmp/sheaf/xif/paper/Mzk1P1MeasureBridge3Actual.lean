import tmp.sheaf.xif.paper.Mzk1NestedInductionActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1MeasureBridge3Actual — general P1 measure laws (real lemmas)

Real Lean (no sorry/axiom): basic Finset laws for the P1-degree measure maxDegP, used in
the P1 measure transfer for the f0 step: union, insert, and monotonicity under subsets.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge3Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

attribute [local instance] Classical.decEq

universe u

/-- P1 maximal degree of a union is the max of the two maximal degrees. -/
theorem maxDegP_union (S T : Finset (P1Point Qbar)) :
    maxDegP (S ∪ T) = max (maxDegP S) (maxDegP T) := by
  unfold maxDegP
  rw [Finset.sup_union]

/-- P1 maximal degree after inserting a point: max of its degree and the old maximum. -/
theorem maxDegP_insert (S : Finset (P1Point Qbar)) (p : P1Point Qbar) :
    maxDegP (insert p S) = max (degP p) (maxDegP S) := by
  unfold maxDegP
  rw [Finset.sup_insert]

/-- P1 maximal degree is monotone under subsets. -/
theorem maxDegP_mono {S T : Finset (P1Point Qbar)} (h : S ⊆ T) :
    maxDegP S <= maxDegP T := by
  unfold maxDegP
  exact Finset.sup_mono h

/-- The finite image has no larger P1 maximal degree than its insert-infinity closure. -/
theorem maxDegP_image_le_insert_infty (S : Finset Qbar) :
    maxDegP (S.image (fun z => P1Point.ofFinite z)) <=
      maxDegP (insert P1Point.infty (S.image (fun z => P1Point.ofFinite z))) :=
  maxDegP_mono (Finset.subset_insert _ _)

/-- Row record. -/
def p1MeasureBridge3Rows : List (String × String) :=
  [ ("maxDegP_union", "PROVED"),
    ("maxDegP_insert", "PROVED"),
    ("maxDegP_mono", "PROVED"),
    ("maxDegP_image_le_insert_infty", "PROVED") ]

theorem p1MeasureBridge3Rows_length : p1MeasureBridge3Rows.length = 4 := rfl

#check maxDegP_union
#check maxDegP_insert
#check maxDegP_mono
#check maxDegP_image_le_insert_infty

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge3Actual
end
