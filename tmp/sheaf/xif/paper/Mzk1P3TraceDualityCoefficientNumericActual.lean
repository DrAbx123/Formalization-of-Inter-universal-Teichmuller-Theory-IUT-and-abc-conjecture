import tmp.sheaf.xif.paper.Mzk1P3TraceDualityCoefficientActual
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P3TraceDualityCoefficientNumericActual
/-- Numeric product form of the componentwise trace-duality coefficient. -/
def traceDualityCoefficientNumeric {ι : Type*} [Fintype ι] (coeff : ι → ℝ) : ℝ :=
  ∏ i, coeff i
theorem traceDualityCoefficientNumeric_pos {ι : Type*} [Fintype ι]
    (coeff : ι → ℝ) (h : ∀ i, 0 < coeff i) :
    0 < traceDualityCoefficientNumeric coeff := by
  unfold traceDualityCoefficientNumeric
  exact Finset.prod_pos (fun i _ => h i)
end LeanFormal.IUT.XiFPaper.Mzk1P3TraceDualityCoefficientNumericActual
end