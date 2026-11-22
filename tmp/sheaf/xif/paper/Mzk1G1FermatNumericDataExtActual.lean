/- G1a Fermat numeric data extension (small). -/
import tmp.sheaf.xif.paper.Mzk1G1FermatNumericDataActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatNumericDataActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatNumericDataExtActual
theorem fermatNumericData_boundary_identity (n : ℕ) :
    (fermatNumericData n).boundary = 3 * (n : ℚ) := rfl
theorem fermatNumericData_canonicalRatio_identity (n : ℕ) (hn : (n : ℚ) ≠ 3) :
    (fermatNumericData n).canonicalRatio = (n : ℚ) / ((n : ℚ) - 3) := rfl
theorem fermatNumericData_euler_identity (n : ℕ) :
    2 - 2 * (fermatNumericData n).genus = -((n : ℚ) * ((n : ℚ) - 3)) := by
  unfold fermatNumericData; ring
#print axioms fermatNumericData_euler_identity
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatNumericDataExtActual
