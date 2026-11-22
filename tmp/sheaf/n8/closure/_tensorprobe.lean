import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition
import Mathlib
open LeanFormal.IUT
open scoped TensorProduct
noncomputable section
variable {p : Nat} [Fact p.Prime] {ι : Type} [Fintype ι]
variable (A : ι → Type) [∀ i, NormedField (A i)] [∀ i, NormedAlgebra ℚ_[p] (A i)]
  [∀ i, FiniteDimensional ℚ_[p] (A i)]
abbrev E := FinitePadicTensor (p := p) A
#check PiTensorProduct.tprod
#check Algebra.lmul
#check Algebra.norm_apply
#check Module.finrank
