import Mathlib
open Module Matrix
noncomputable section
namespace ProbeToMatrixDiag
variable {p : Nat} [Fact p.Prime]
variable {E : Type*} [AddCommGroup E] [Module ℚ_[p] E]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem toMatrix_eq_diagonal_mul
    (f : E →ₗ[ℚ_[p]] E) (bM bN : Basis n ℚ_[p] E)
    (a : n → ℚ_[p]) (D : Matrix n n ℚ_[p])
    (hB : ∀ i, bN i = a i • bM i)
    (hD : ∀ i, f (bM i) = ∑ j, D j i • bN j) :
    LinearMap.toMatrix bM bM f = Matrix.diagonal a * D := by
  have hrepr : ∀ x, bM.repr (bN x) = Finsupp.single x (a x) := by
    intro x
    rw [hB x, map_smul, Basis.repr_self]
    simp
  ext j i
  rw [LinearMap.toMatrix_apply, hD i, map_sum]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · rw [hrepr j]
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
    ring
  · intro x hx hxj
    rw [hrepr x]
    ext k
    simp [Finsupp.mul_apply, hxj, hxj.symm]
  · intro hj
    simp at hj
end ProbeToMatrixDiag
