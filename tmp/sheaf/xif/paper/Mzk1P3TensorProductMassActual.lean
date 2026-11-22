import Mathlib.Analysis.SpecialFunctions.Log.Basic
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P3TensorProductMassActual
/-- Product mass of a finite family of positive masses. -/
def tensorProductMass {ι : Type*} [Fintype ι] (m : ι → ℝ) : ℝ := ∏ i, m i
theorem log_tensorProductMass {ι : Type*} [Fintype ι] (m : ι → ℝ)
    (hpos : ∀ i, 0 < m i) :
    Real.log (tensorProductMass m) = ∑ i, Real.log (m i) := by
  unfold tensorProductMass
  rw [Real.log_prod]
  intro i _
  exact (hpos i).ne'
end LeanFormal.IUT.XiFPaper.Mzk1P3TensorProductMassActual
end