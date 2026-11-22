import Mathlib.LinearAlgebra.PiTensorProduct.DirectSum
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Algebra.Algebra.Pi

/-!
# A tensor of finite products, with its tuple labels retained

The equivalence is constructed from the proved direct-sum distribution and
the finite direct-sum/product equivalences. Its pure-tensor evaluation is the
coordinatewise tensor. Multiplicativity is proved on actual tensor generators.
-/

namespace LeanFormal.IUT.FiniteTensorProductDistribution

open scoped TensorProduct

noncomputable section

variable (R : Type*) [CommSemiring R] {ι : Type*} [Fintype ι]
variable {κ : ι → Type*} [∀ i, Fintype (κ i)] (M : (i : ι) → κ i → Type*)

section Modules

variable [∀ i j, AddCommMonoid (M i j)] [∀ i j, Module R (M i j)]

def tensorProductLinearEquiv :
    (⨂[R] i, ((j : κ i) → M i j)) ≃ₗ[R] ((tuple : (i : ι) → κ i) → ⨂[R] i, M i (tuple i)) := by
  classical
  exact (PiTensorProduct.congr
    (fun i => (DirectSum.linearEquivFunOnFintype R (κ i) (M i)).symm)).trans
    (PiTensorProduct.ofDirectSumEquiv.trans
      (DirectSum.linearEquivFunOnFintype R ((i : ι) → κ i) (fun tuple => ⨂[R] i, M i (tuple i))))

theorem tensorProductLinearEquiv_tprod (x : (i : ι) → (j : κ i) → M i j)
    (tuple : (i : ι) → κ i) :
    tensorProductLinearEquiv R M (PiTensorProduct.tprod R x) tuple =
      PiTensorProduct.tprod R (fun i => x i (tuple i)) := by
  classical
  simp only [tensorProductLinearEquiv, LinearEquiv.trans_apply, PiTensorProduct.congr_tprod,
    DirectSum.linearEquivFunOnFintype_apply, PiTensorProduct.ofDirectSumEquiv_tprod_apply]
  congr 1

end Modules

section Algebras

variable [∀ i j, CommSemiring (M i j)] [∀ i j, Algebra R (M i j)]

theorem tensorProductLinearEquiv_map_one : tensorProductLinearEquiv R M 1 = 1 := by
  ext tuple
  change tensorProductLinearEquiv R M (PiTensorProduct.tprod R (fun _ => 1)) tuple = _
  rw [tensorProductLinearEquiv_tprod]
  rfl

theorem tensorProductLinearEquiv_map_mul (x y : ⨂[R] i, ((j : κ i) → M i j)) :
    tensorProductLinearEquiv R M (x * y) =
      tensorProductLinearEquiv R M x * tensorProductLinearEquiv R M y := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s g =>
      ext tuple
      simp only [smul_mul_smul_comm, map_smul, PiTensorProduct.tprod_mul_tprod,
        tensorProductLinearEquiv_tprod, Pi.smul_apply, Pi.mul_apply]
      rfl
    | add y z hy hz =>
      simp only [mul_add, map_add, hy, hz]
  | add x z hx hz =>
    simp only [add_mul, map_add, hx, hz]

def tensorProductAlgEquiv :
    (⨂[R] i, ((j : κ i) → M i j)) ≃ₐ[R] ((tuple : (i : ι) → κ i) → ⨂[R] i, M i (tuple i)) :=
  AlgEquiv.ofLinearEquiv (tensorProductLinearEquiv R M)
    (tensorProductLinearEquiv_map_one R M) (tensorProductLinearEquiv_map_mul R M)

theorem tensorProductAlgEquiv_tprod (x : (i : ι) → (j : κ i) → M i j)
    (tuple : (i : ι) → κ i) :
    tensorProductAlgEquiv R M (PiTensorProduct.tprod R x) tuple =
      PiTensorProduct.tprod R (fun i => x i (tuple i)) :=
  tensorProductLinearEquiv_tprod R M x tuple

end Algebras

end

end LeanFormal.IUT.FiniteTensorProductDistribution
