/- The P8 uniform-height input (additive height bound) is equivalent to ABC. -/
import tmp.sheaf.xif.paper.Mzk1P8FromP6IVInequalityActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightInputEquivActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVInequalityActual

theorem p8Input_iff_ABC : P8P6IVInequalityInput ↔ ABCConjecture :=
  (LeanFormal.IUT.abcConjecture_iff_abcArithmeticWeightHeightBound).symm
theorem p8Input_of_ABC (h : ABCConjecture) : P8P6IVInequalityInput :=
  (LeanFormal.IUT.abcConjecture_iff_abcArithmeticWeightHeightBound).mp h
#print axioms p8Input_iff_ABC
end LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightInputEquivActual
end
