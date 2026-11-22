import tmp.sheaf.xif.paper.Mzk1P8UniformHeightActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P8FromSandwichFinal
/-- P8 final consumer: the uniform height bound gives ABC. -/
theorem p8_fromSandwichFinal_abc (h : P8UniformHeightBound) : ABCConjecture :=
  p8UniformHeight_consumer h
#print axioms p8_fromSandwichFinal_abc
end LeanFormal.IUT.XiFPaper.Mzk1P8FromSandwichFinal
end