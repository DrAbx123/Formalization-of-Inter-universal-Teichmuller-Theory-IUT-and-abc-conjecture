import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
/-! GAP-DET-HAAR diagonal determinant norm facts -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarDiagonalNormActual
variable {p : Nat} [Fact p.Prime]
/-- p-adic norm of a p-power. -/
theorem norm_p_pow (e : Nat) :
    ‖((p : ℚ_[p]) ^ e)‖ = (p : Real) ^ (-(e : Real)) := by
  rw [Padic.norm_p_pow]
  rw [← Real.rpow_neg_natCast]
/-- Norm of a product of p-powers. -/
theorem norm_prod_p_pow {d : Type*} [Fintype d] (e : d -> Nat) :
    ‖(∏ i, ((p : ℚ_[p]) ^ e i))‖ =
      (∏ i, ((p : Real) ^ e i))⁻¹ := by
  rw [norm_prod]
  simp_rw [norm_p_pow]
  simp_rw [Real.rpow_neg (by positivity : (0 : Real) <= (p : Real))]
  rw [Finset.prod_inv_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.rpow_natCast]
/-- Missing: identify a diagonal SNF factor's Haar scaling with the norm of
the determinant product. -/
def diagonalNormMissing : List String :=
  [ "diagonal factor D is diagonal in an actual Z_p basis",
    "det norm bridge from the diagonal determinant formula" ]
theorem diagonalNormMissing_length : diagonalNormMissing.length = 2 := rfl
#check norm_p_pow
#check norm_prod_p_pow
end LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarDiagonalNormActual
end
