import tmp.sheaf.xif.paper.Mzk1P6IVActual
import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage
import Mathlib.Tactic

set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open LeanFormal.IUT.XiFPaper.Mzk1P6IVActual

namespace LeanFormal.IUT.XiFPaper.Mzk1P6PaperBoundActual

/-- Paper StepV procession bound in the exact `(l+5)/4 D - (l+1)/24 Q + S + (l+5)T` form. -/
noncomputable def p6PaperBound (n : Nat) (D Q S T : Real) : Real :=
  ((2 * (n : Real) + 1) + 5) / 4 * D -
    ((2 * (n : Real) + 1) + 1) / 24 * Q + S +
    ((2 * (n : Real) + 1) + 5) * T

/-- Exact identification: the StepV averaged readout equals the paper bound. -/
theorem p6IVR_eq_paperBound (n : Nat) (hn : 1 ≤ n) (D Q S T : Real) :
    p6IVR n D Q S T = p6PaperBound n D Q S T := by
  unfold p6IVR p6PaperBound
  rw [show 2 * (n : Real) + 1 = 2 * (n : Real) + 1 from rfl]
  exact processionAverage_eq n hn D Q S T

/-- The averaged readout is at most the paper bound. -/
theorem p6IVR_le_paperBound (n : Nat) (hn : 1 ≤ n) (D Q S T : Real) :
    p6IVR n D Q S T ≤ p6PaperBound n D Q S T :=
  le_of_eq (p6IVR_eq_paperBound n hn D Q S T)

/-- The paper bound is bounded by the normalized procession upper bound. -/
theorem p6PaperBound_le_processionUpper
    (n : Nat) (hn : 2 ≤ n) (D Q S T : Real)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    p6PaperBound n D Q S T ≤
      ((2 * (n : Real) + 1) + 1) / 4 *
        ((1 + 4 / (2 * (n : Real) + 1)) * D - Q / 6 +
          4 / (2 * (n : Real) + 1) * S + 20 / 3 * T) := by
  rw [← p6IVR_eq_paperBound n (by omega) D Q S T]
  exact processionAverage_le n hn D Q S T hD hS hT

#print axioms p6IVR_eq_paperBound
#print axioms p6IVR_le_paperBound
#print axioms p6PaperBound_le_processionUpper

end LeanFormal.IUT.XiFPaper.Mzk1P6PaperBoundActual
end