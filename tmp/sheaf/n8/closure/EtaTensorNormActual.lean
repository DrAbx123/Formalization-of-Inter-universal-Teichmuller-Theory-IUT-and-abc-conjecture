import tmp.sheaf.n8.closure.EtaTensorBlockDetActual

/-!
# Eta tensor norm: exact gap and conditional BPS determinant

EtaTensorBlockDetActual constructed the actual tensor block/action and proved

  tensorDet = Algebra.norm Q_p (tensorUnit).

The remaining BPS step is the tensor-norm multiplicativity

  Algebra.norm Q_p (tensorUnit) = Norm(g) ^ (D / d_j).

Mathlib has the norm transitivity theorem (Algebra.norm_norm), but no theorem
identifying the algebra norm of a pure tensor in a PiTensorProduct with the
factor norm raised to the product of the other dimensions.  We record the exact
conditional implication and the missing Mathlib theorem; no arbitrary norm
factor is introduced.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.N8Closure.EtaTensorNormActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.EtaTensorBlockDetActual

universe u

variable {p : Nat} [Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
  [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]

/-- Exact missing Mathlib theorem: the algebra norm of the pure tensor is the
factor norm raised to D/d_j. -/
def TensorNormMultiplicativityTheorem (j : ι) (g : A j) : Prop :=
  Algebra.norm ℚ_[p] (tensorUnit (p := p) A j g) =
    (Algebra.norm ℚ_[p] g) ^
      (totalDim (p := p) A / factorDim (p := p) A j)

/-- The same statement is exactly TensorNormMultiplicativityGap. -/
theorem tensorNormMultiplicativityTheorem_iff_gap (j : ι) (g : A j) :
    TensorNormMultiplicativityTheorem (p := p) A j g ↔
      TensorNormMultiplicativityGap (p := p) A j g :=
  Iff.rfl

/-- Conditional actual BPS determinant: once the missing tensor-norm theorem is
supplied, the actual tensorDet computation closes the BPS formula. -/
theorem tensorBlockDetTarget_of_tensorNormMultiplicativity
    (j : ι) (g : A j)
    (h : TensorNormMultiplicativityTheorem (p := p) A j g) :
    TensorBlockDetTarget (p := p) A j g := by
  rw [tensorBlockDetTarget_iff_normGap]
  exact h

/-- Exact no-go boundary: Mathlib has Algebra.norm_norm (tower transitivity)
but no pure-tensor norm formula for PiTensorProduct. -/
def MissingMathlibTensorNormTheorem : Prop :=
  ∀ (j : ι) (g : A j), TensorNormMultiplicativityTheorem (p := p) A j g

/-- The missing theorem is not assumed; only the conditional implication above
is provided. -/
def BPSDetTargetRemainingGap : Prop :=
  ∃ (j : ι) (g : A j), ¬ TensorNormMultiplicativityTheorem (p := p) A j g

end LeanFormal.IUT.N8Closure.EtaTensorNormActual
