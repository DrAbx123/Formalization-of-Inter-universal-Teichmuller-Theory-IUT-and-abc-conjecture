import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
open Matrix
open scoped Matrix
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sum_smul_single_one (y : ι → R) : (∑ j, y j • (Pi.single j (1 : R))) = y := by
  have h : ∀ j, y j • (Pi.single j (1 : R)) = Pi.single j (y j) := by
    intro j; funext i; simp [Pi.smul_apply, Pi.single_apply]
  simp only [h]
  exact Finset.univ_sum_single y

lemma dotProduct_mulVec_assoc (x y : ι → R) (N : Matrix ι ι R) :
    x ⬝ᵥ (N *ᵥ y) = (Nᵀ *ᵥ x) ⬝ᵥ y := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

example (N : Matrix ι ι R) (h : IsUnit N.det) : IsUnit Nᵀ.det := by
  rwa [Matrix.det_transpose]
