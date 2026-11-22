import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Cache the proved dimension product at the abstract Qp field-tower interface. -/

namespace LeanFormal.IUT.LocalFieldPadicTensor

noncomputable section

variable {p : ℕ} [Fact p.Prime]
variable (L M : Type*) [Semiring L] [AddCommMonoid M]
variable [lowerModule : Module ℚ_[p] L] [relativeModule : Module L M]
variable [absoluteModule : Module ℚ_[p] M]
variable [@IsScalarTower ℚ_[p] L M lowerModule.toSMul relativeModule.toSMul absoluteModule.toSMul]
variable [StrongRankCondition L] [Module.Free ℚ_[p] L] [Module.Free L M]

theorem finrank_padicFieldTower :
    Module.finrank ℚ_[p] L * Module.finrank L M = Module.finrank ℚ_[p] M :=
  Module.finrank_mul_finrank ℚ_[p] L M

end

end LeanFormal.IUT.LocalFieldPadicTensor
