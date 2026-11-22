import Mathlib.LinearAlgebra.PiTensorProduct.Basic
noncomputable section
open scoped TensorProduct
universe u v
variable {ι : Type u} [Fintype ι] (M : ι → Type v)
variable [∀ i, AddCommGroup (M i)] [∀ i, Module ℚ (M i)] [∀ i, Module ℚ_[5] (M i)]
variable [∀ i, IsScalarTower ℚ ℚ_[5] (M i)]
local instance : Module ℚ (⨂[ℚ_[5]] i, M i) := Module.restrictScalars ℚ ℚ_[5] _
noncomputable def ratToQp : (⨂[ℚ] i, M i) →ₗ[ℚ] (⨂[ℚ_[5]] i, M i) :=
  PiTensorProduct.lift
    { toFun := fun x => PiTensorProduct.tprod ℚ_[5] x
      map_add' := by
        intro i x y
        exact (PiTensorProduct.tprod ℚ_[5] M).map_add i x y
      map_smul' := by
        intro i c x
        simpa [PiTensorProduct.tprod] using
          (PiTensorProduct.tprod ℚ_[5] M).map_smul i (algebraMap ℚ ℚ_[5] c) x }
#check ratToQp
end
