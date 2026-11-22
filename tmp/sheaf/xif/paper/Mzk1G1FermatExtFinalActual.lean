/- G1a numeric ext final. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatNumericDataExtActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatNumericDataActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatNumericDataExtActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatExtFinalActual
theorem fermat_ext_euler_final (n : Nat) :
    2 - 2 * (fermatNumericData n).genus = -((n : Rat) * ((n : Rat) - 3)) := by
  exact fermatNumericData_euler_identity n
theorem fermat_ext_boundary_final (n : Nat) :
    (fermatNumericData n).boundary = 3 * (n : Rat) := rfl
#print axioms fermat_ext_euler_final
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatExtFinalActual
