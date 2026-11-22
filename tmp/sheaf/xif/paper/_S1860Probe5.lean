import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
open Matrix
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

example (N : Matrix ι ι R) (h : IsUnit N.det) : IsUnit Nᵀ.det := by
  rwa [Matrix.det_transpose]

example (v : ι → R) (M : Matrix ι ι R) : Matrix.vecMul v M = Mᵀ *ᵥ v := by
  ext j
  simp [Matrix.vecMul, Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply, mul_comm]

example (y : ι → R) : (∑ j, y j • (Pi.single j (1 : R))) = y := by
  funext i
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · intro hi
    simp at hi
