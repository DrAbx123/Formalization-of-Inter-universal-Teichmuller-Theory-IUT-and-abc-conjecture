import Mathlib.FieldTheory.SplittingField.Construction

open Polynomial

namespace Probe0
variable (f : ℚ[X])
#check Polynomial.IsSplittingField.splittingField f
example : IsSplittingField ℚ (Polynomial.SplittingField f) f := Polynomial.IsSplittingField.splittingField f
example : IsSplittingField ℚ (Polynomial.SplittingField f) f := inferInstance
end Probe0
