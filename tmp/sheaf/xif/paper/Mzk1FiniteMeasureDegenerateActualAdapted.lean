import tmp.sheaf.xif.paper.Mzk1FiniteMeasureLawsActualAdapted

/-! # Mzk1FiniteMeasureDegenerateActualAdapted — degenerate finite measure values (real)

Real Lean (no sorry/axiom): empty and singleton values of the finite-part max-degree.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureDegenerateActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActualAdapted

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_empty : maxDeg (∅ : Finset Qbar) = 0 := by
  unfold maxDeg
  simp

theorem maxDeg_singleton (x : Qbar) : maxDeg {x} = degQ x := by
  unfold maxDeg
  rw [Finset.sup_singleton]

def finiteMeasureDegenerateRows : List (String × String) :=
  [ ("maxDeg_empty", "PROVED"), ("maxDeg_singleton", "PROVED") ]

theorem finiteMeasureDegenerateRows_length : finiteMeasureDegenerateRows.length = 2 := rfl

#check maxDeg_empty
#check maxDeg_singleton

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureDegenerateActualAdapted
end
