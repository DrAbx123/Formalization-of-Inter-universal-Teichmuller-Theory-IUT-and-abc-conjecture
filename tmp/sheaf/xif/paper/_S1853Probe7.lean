import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties

noncomputable section
open LinearMap
open scoped Matrix

namespace Probe1853

#check @single_one_dotProduct
#check @dotProduct_single_one

lemma Matrix.toBilin'_nondegenerate_of_isUnit_det
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (h : IsUnit M.det) :
    (Matrix.toBilin' M).Nondegenerate := by
  constructor
  · intro x hx
    have hmul : Mᵀ *ᵥ x = 0 := by
      ext j
      have h := hx (Pi.single j 1)
      rw [Matrix.toBilin'_apply', Matrix.mulVec_single_one] at h
      simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm, mul_left_comm, mul_assoc] using h
    calc x = (1 : Matrix ι ι R) *ᵥ x := by simp
      _ = ((M⁻¹)ᵀ * Mᵀ) *ᵥ x := by
        rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv M h]
        simp
      _ = (M⁻¹)ᵀ *ᵥ (Mᵀ *ᵥ x) := by rw [← Matrix.mulVec_mulVec]
      _ = 0 := by rw [hmul, Matrix.mulVec_zero]
  · intro y hy
    have hmul : M *ᵥ y = 0 := by
      ext i
      have h := hy (Pi.single i 1)
      rw [Matrix.toBilin'_apply', single_one_dotProduct] at h
      simpa using h
    calc y = (1 : Matrix ι ι R) *ᵥ y := by simp
      _ = (M⁻¹ * M) *ᵥ y := by
        rw [Matrix.nonsing_inv_mul M h]
      _ = M⁻¹ *ᵥ (M *ᵥ y) := by rw [← Matrix.mulVec_mulVec]
      _ = 0 := by rw [hmul, Matrix.mulVec_zero]

lemma nondegenerate_of_isUnit_det
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R M)
    (B : LinearMap.BilinForm R M) (h : IsUnit ((LinearMap.BilinForm.toMatrix b) B).det) :
    B.Nondegenerate := by
  have h' : (Matrix.toBilin' ((LinearMap.BilinForm.toMatrix b) B)).Nondegenerate :=
    Matrix.toBilin'_nondegenerate_of_isUnit_det _ h
  have hcongr : (LinearMap.BilinForm.congr b.equivFun) B =
      Matrix.toBilin' ((LinearMap.BilinForm.toMatrix b) B) := by
    apply LinearMap.BilinForm.ext
    intro x y
    rw [LinearMap.BilinForm.congr_apply]
    rw [Matrix.toBilin'_apply']
    exact (LinearMap.BilinForm.dotProduct_toMatrix_mulVec (b := b) (B := B) (x := x) (y := y)).symm
  rw [← hcongr] at h'
  exact (LinearMap.BilinForm.nondegenerate_congr_iff b.equivFun).mp h'

end Probe1853