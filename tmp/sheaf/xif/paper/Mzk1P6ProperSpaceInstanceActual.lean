import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Field.Basic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6ProperSpaceInstanceActual

/-- A finite-dimensional normed algebra over a complete nonarchimedean base is proper. -/
theorem properSpace_of_finiteDimensional
    {p : Nat} [Fact p.Prime] (E : Type*) [NormedField E]
    [NormedAlgebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] : ProperSpace E :=
  FiniteDimensional.proper ℚ_[p] E

end LeanFormal.IUT.XiFPaper.Mzk1P6ProperSpaceInstanceActual
end