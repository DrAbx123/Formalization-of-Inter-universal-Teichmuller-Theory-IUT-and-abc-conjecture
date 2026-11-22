import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge16Actual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1MeasureBridge17Actual — cardinality corollaries (real)

Real Lean (no sorry/axiom): combined cardinality bounds for the P1 measure used to estimate
the concrete f0 step target.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge17Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge9Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge3Actual

attribute [local instance] Classical.decEq

universe u

theorem numMaxP_insert_le_card_succ (S : Finset (P1Point Qbar)) (p : P1Point Qbar) :
    numMaxP (insert p S) <= S.card + 1 := by
  have h := numMaxP_le_card (insert p S)
  rw [Finset.card_insert_of_not_mem] at h
  · omega
  · by_contra hmem
    have : p ∈ insert p S := Finset.mem_insert_self p S
    exact hmem this

theorem maxDegP_union_le_card_add (S T : Finset (P1Point Qbar)) :
    maxDegP (S ∪ T) <= (S ∪ T).card + 1 := by
  rw [maxDegP_union_le_sum]
  have hS := numMaxP_le_card (S ∪ T)
  omega

def p1MeasureBridge17Rows : List (String × String) :=
  [ ("numMaxP_insert_le_card_succ", "PROVED"), ("maxDegP_union_le_card_add", "PROVED") ]

theorem p1MeasureBridge17Rows_length : p1MeasureBridge17Rows.length = 2 := rfl

#check numMaxP_insert_le_card_succ

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge17Actual
end
