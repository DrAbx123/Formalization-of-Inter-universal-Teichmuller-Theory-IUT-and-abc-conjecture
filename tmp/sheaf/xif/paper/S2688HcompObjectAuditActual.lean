import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open Real

namespace LeanFormal.IUT.XiFPaper.S2688HcompObjectAuditActual

/-- The exact hcomp scalar object of the paper route. -/
def S2688HcompObject (average badQAbsLog : Real) : Prop :=
  average ≤ badQAbsLog

theorem S2688HcompObject_iff_two_le_order
    (average : Real) (order : Nat)
    (haverage : average = 2 * Real.log 5) :
    S2688HcompObject average ((order : Real) * Real.log 5) ↔ 2 ≤ order := by
  unfold S2688HcompObject
  rw [haverage]
  have hlog : 0 < Real.log (5 : Real) :=
    Real.log_pos (by norm_num : (1 : Real) < 5)
  constructor
  · intro h
    have h' : (2 : Real) ≤ (order : Real) :=
      le_of_mul_le_mul_right (by simpa [mul_comm] using h) hlog
    exact_mod_cast h'
  · intro h
    have h2 : (2 : Real) ≤ (order : Real) := by exact_mod_cast h
    exact mul_le_mul_of_nonneg_right h2 (le_of_lt hlog)

def S2688HqObject (concreteQLog paperQLog : Real) : Prop :=
  concreteQLog = paperQLog

#check S2688HcompObject
#check S2688HcompObject_iff_two_le_order
#check S2688HqObject
#print axioms S2688HcompObject_iff_two_le_order
end LeanFormal.IUT.XiFPaper.S2688HcompObjectAuditActual
end