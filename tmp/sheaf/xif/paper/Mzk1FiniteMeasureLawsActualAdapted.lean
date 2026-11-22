import tmp.sheaf.xif.paper.Mzk1NestedInductionActual

/-! # Mzk1FiniteMeasureLawsActualAdapted — finite-part measure laws (real, self-contained)

Real Lean (no sorry/axiom): elementary Finset laws for the finite-part measure maxDeg/numMax
of Mzk1NestedInductionActual, reusable when bounding concrete step targets.  Registry 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual

attribute [local instance] Classical.decEq

universe u

/-- Finite max-degree of a union is the max of the two. -/
theorem maxDeg_union (S T : Finset Qbar) : maxDeg (S ∪ T) = max (maxDeg S) (maxDeg T) := by
  unfold maxDeg
  rw [Finset.sup_union]

/-- Finite max-degree after inserting a point. -/
theorem maxDeg_insert (S : Finset Qbar) (x : Qbar) :
    maxDeg (insert x S) = max (degQ x) (maxDeg S) := by
  unfold maxDeg
  rw [Finset.sup_insert]

/-- Finite max-degree is monotone under subsets. -/
theorem maxDeg_mono {S T : Finset Qbar} (h : S ⊆ T) : maxDeg S <= maxDeg T := by
  unfold maxDeg
  exact Finset.sup_mono h

/-- Finite maximal count is at most the cardinality. -/
theorem numMax_le_card (S : Finset Qbar) : numMax S <= S.card := by
  unfold numMax
  exact Finset.card_filter_le _ _

/-- Row record. -/
def finiteMeasureLawsRows : List (String × String) :=
  [ ("maxDeg_union", "PROVED"), ("maxDeg_insert", "PROVED"),
    ("maxDeg_mono", "PROVED"), ("numMax_le_card", "PROVED") ]

theorem finiteMeasureLawsRows_length : finiteMeasureLawsRows.length = 4 := rfl

#check maxDeg_union
#check numMax_le_card

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActualAdapted
end
