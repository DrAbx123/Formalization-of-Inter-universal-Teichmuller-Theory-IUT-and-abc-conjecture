import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basic
noncomputable section
open scoped TensorProduct
open LinearMap

section
variable {R S X : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup X] [Module R X]

example (s : S) (x : X) (c : R) :
    s ⊗ₜ[R] (c • x) = (s * algebraMap R S c) • (1 ⊗ₜ[R] x) := by
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
    TensorProduct.smul_tmul', Algebra.smul_def]
  simp [mul_comm]

end
