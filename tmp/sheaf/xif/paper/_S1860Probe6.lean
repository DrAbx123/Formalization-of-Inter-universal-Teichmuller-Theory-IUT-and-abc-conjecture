import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
open Matrix
open scoped Matrix
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

#check @dotProduct
#check @Matrix.vecMul
#check @Matrix.mulVec
#check @Pi.single_eq_of_ne
#check @Finset.univ_sum_single

example (y : ι → R) : (∑ j, y j • (Pi.single j (1 : R))) = y := by
  funext i
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, mul_zero]
  · intro hi
    simp at hi

example (x y : ι → R) (N : Matrix ι ι R) : x ⬝ᵥ (N *ᵥ y) = (Nᵀ *ᵥ x) ⬝ᵥ y := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
