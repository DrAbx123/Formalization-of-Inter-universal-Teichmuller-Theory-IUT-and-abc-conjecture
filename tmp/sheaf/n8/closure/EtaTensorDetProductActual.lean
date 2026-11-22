import Mathlib

/-!
# Tensor determinant product (actual binary case)

Mathlib proves the matrix of a binary tensor product map is the Kronecker
product (TensorProduct.toMatrix_map).  Using determinant of Kronecker products,
we prove the actual determinant formula

  det(f (x) g) = det(f) ^ dim N * det(g) ^ dim M.

Specializing g = id gives the BPS factor

  det(id (x) f) = det(f) ^ dim N.

This is the actual determinant core.  The remaining BPS step is a linear
equivalence between the production FinitePadicTensor and this binary
tensor decomposition preserving the action; no arbitrary factor is used.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
open scoped TensorProduct Kronecker

namespace LeanFormal.IUT.N8Closure.EtaTensorDetProductActual

open Matrix Module LinearMap

universe u v w

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Actual determinant of a binary tensor product of endomorphisms. -/
theorem det_tensorProduct_map (bM : Basis ι R M) (bN : Basis κ R N)
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    LinearMap.det (TensorProduct.map f g) =
      (LinearMap.det f) ^ Fintype.card κ *
        (LinearMap.det g) ^ Fintype.card ι := by
  rw [← LinearMap.det_toMatrix (bM.tensorProduct bN)
    (TensorProduct.map f g)]
  rw [TensorProduct.toMatrix_map]
  rw [Matrix.det_kronecker]
  rw [LinearMap.det_toMatrix bM f, LinearMap.det_toMatrix bN g]

/-- The BPS isotropic case: id on the left tensor factor and f on the right. -/
theorem det_id_tensorProduct_map (bM : Basis ι R M) (bN : Basis κ R N)
    (f : N →ₗ[R] N) :
    LinearMap.det (TensorProduct.map (LinearMap.id : M →ₗ[R] M) f) =
      (LinearMap.det f) ^ Fintype.card ι := by
  rw [det_tensorProduct_map bM bN LinearMap.id f, LinearMap.det_id]
  simp

/-- Exact remaining BPS interface: a linear equivalence from the production
FinitePadicTensor to the binary tensor decomposition, intertwining the pure
tensor action.  No such equivalence is fabricated here. -/
structure TensorBinaryDecomposition (E : Type*) [AddCommGroup E] [Module R E] where
  left : Type v
  [leftAdd : AddCommGroup left]
  [leftModule : Module R left]
  right : Type w
  [rightAdd : AddCommGroup right]
  [rightModule : Module R right]
  equiv : E ≃ₗ[R] TensorProduct R left right
  action : E →ₗ[R] E
  binaryAction : TensorProduct R left right →ₗ[R] TensorProduct R left right
  action_compat : ∀ x, equiv (action x) = binaryAction (equiv x)

attribute [instance] TensorBinaryDecomposition.leftAdd
  TensorBinaryDecomposition.leftModule TensorBinaryDecomposition.rightAdd
  TensorBinaryDecomposition.rightModule

end LeanFormal.IUT.N8Closure.EtaTensorDetProductActual
