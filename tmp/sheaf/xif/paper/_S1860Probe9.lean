import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basic
noncomputable section
open scoped TensorProduct
open LinearMap

section
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

example (g : M →ₗ[R] R) : S →ₗ[S] (M →ₗ[R] S) :=
  ((LinearMap.lsmul S (M →ₗ[R] S)).flip) ((Algebra.linearMap R S).comp g)

example (g : M →ₗ[R] R) : (S ⊗[R] M) →ₗ[S] S :=
  TensorProduct.AlgebraTensorModule.lift
    (((LinearMap.lsmul S (M →ₗ[R] S)).flip) ((Algebra.linearMap R S).comp g))

example (g : M →ₗ[R] R) (s : S) (m : M) :
    (TensorProduct.AlgebraTensorModule.lift
      (((LinearMap.lsmul S (M →ₗ[R] S)).flip) ((Algebra.linearMap R S).comp g)))
        (s ⊗ₜ[R] m) = s * algebraMap R S (g m) := by
  rw [TensorProduct.AlgebraTensorModule.lift_tmul]
  simp
end
