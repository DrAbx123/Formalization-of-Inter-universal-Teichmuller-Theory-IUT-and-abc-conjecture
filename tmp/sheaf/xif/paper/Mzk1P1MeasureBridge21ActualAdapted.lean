import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge20ActualAdapted
import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge18ActualAdapted

/-! # Mzk1P1MeasureBridge21ActualAdapted — infinity-insertion distribution (real)

Real Lean (no sorry/axiom): inserting infinity distributes over unions in the P1 degree
measure.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge21ActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge3Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge18ActualAdapted
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge20ActualAdapted

attribute [local instance] Classical.decEq

universe u

theorem maxDegP_insert_infty_union (S T : Finset (P1Point Qbar)) :
    maxDegP (insert P1Point.infty (S ∪ T)) =
      max 1 (max (maxDegP S) (maxDegP T)) := by
  rw [maxDegP_insert_union]
  rfl

theorem maxDegP_union_insert_infty (S T : Finset (P1Point Qbar)) :
    maxDegP (S ∪ insert P1Point.infty T) =
      max (maxDegP S) (max 1 (maxDegP T)) := by
  rw [maxDegP_union_insert]
  rfl

def p1MeasureBridge21Rows : List (String × String) :=
  [ ("maxDegP_insert_infty_union", "PROVED"),
    ("maxDegP_union_insert_infty", "PROVED") ]

theorem p1MeasureBridge21Rows_length : p1MeasureBridge21Rows.length = 2 := rfl

#check maxDegP_insert_infty_union

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge21ActualAdapted
end
