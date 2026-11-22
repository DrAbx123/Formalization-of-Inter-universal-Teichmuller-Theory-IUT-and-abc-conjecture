import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition
import Mathlib

/-!
# ETA tensor block determinant: actual construction

For finite field factors A_i / Q_p, E = tensor_i A_i is the production
FinitePadicTensor.  For g in A_j, the pure tensor
t = 1 (x) ... (x) g (x) ... (x) 1 acts on E by multiplication.  This is the
actual linear map A = id (x) ... (x) mult(g) (x) ... (x) id.

The determinant is identified with the algebra norm of t by
Algebra.norm_apply.  The BPS expected form

  det(A) = Norm(g) ^ (D / d_j),  D = prod_i d_i, d_j = [A_j:Q_p],

is recorded as the exact remaining tensor-norm multiplicativity target.
No arbitrary action or exponent is introduced.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaTensorBlockDetActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open scoped TensorProduct

universe u

variable {p : Nat} [Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
  [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]

/-- Actual finite tensor block E = tensor_i A_i. -/
abbrev TensorBlock : Type := FinitePadicTensor (p := p) A

/-- Actual pure tensor with g in the j-th factor and 1 elsewhere. -/
noncomputable def tensorUnit (j : ι) (g : A j) : TensorBlock (p := p) A :=
  PiTensorProduct.tprod ℚ_[p]
    (fun i => if h : i = j then h ▸ g else (1 : A i))

/-- Actual tensor-block action: multiplication by the pure tensor. -/
noncomputable def tensorAction (j : ι) (g : A j) :
    TensorBlock (p := p) A →ₗ[ℚ_[p]] TensorBlock (p := p) A :=
  Algebra.lmul ℚ_[p] (TensorBlock (p := p) A)
    (tensorUnit (p := p) A j g)

/-- Actual determinant of the tensor-block action. -/
noncomputable def tensorDet (j : ι) (g : A j) : ℚ_[p] :=
  LinearMap.det (tensorAction (p := p) A j g)

/-- Actual identification: tensor determinant = algebra norm of the pure tensor. -/
theorem tensorDet_eq_algebraNorm (j : ι) (g : A j) :
    tensorDet (p := p) A j g =
      Algebra.norm ℚ_[p] (tensorUnit (p := p) A j g) := by
  unfold tensorDet tensorAction
  rw [Algebra.norm_apply]

/-- Factor dimensions and total dimension D. -/
def factorDim (i : ι) : Nat := Module.finrank ℚ_[p] (A i)

def totalDim : Nat := ∏ i, factorDim (p := p) A i

/-- Exact BPS determinant target. -/
def TensorBlockDetTarget (j : ι) (g : A j) : Prop :=
  tensorDet (p := p) A j g =
    (Algebra.norm ℚ_[p] g) ^ (totalDim (p := p) A / factorDim (p := p) A j)

/-- Exact missing production theorem: multiplicativity of the algebra norm on
the pure tensor, equivalently det(id (x) mult(g)) = Norm(g)^(D/d_j).
No arbitrary tensor-norm factor is assumed. -/
def TensorNormMultiplicativityGap (j : ι) (g : A j) : Prop :=
  Algebra.norm ℚ_[p] (tensorUnit (p := p) A j g) =
    (Algebra.norm ℚ_[p] g) ^ (totalDim (p := p) A / factorDim (p := p) A j)

theorem tensorBlockDetTarget_iff_normGap (j : ι) (g : A j) :
    TensorBlockDetTarget (p := p) A j g ↔
      TensorNormMultiplicativityGap (p := p) A j g := by
  rw [TensorBlockDetTarget, TensorNormMultiplicativityGap,
    tensorDet_eq_algebraNorm]

end LeanFormal.IUT.N8Closure.EtaTensorBlockDetActual
