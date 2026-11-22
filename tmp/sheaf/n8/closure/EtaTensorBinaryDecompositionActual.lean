import tmp.sheaf.n8.closure.EtaTensorDetProductActual
import tmp.sheaf.n8.closure.EtaTensorBlockDetActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition

/-!
# Eta tensor binary decomposition: exact gap

Mathlib provides the reindexing and binary tensor splittings separately, but
no assembled theorem gives a linear equivalence from the production
FinitePadicTensor to a binary tensor decomposition preserving the pure-tensor
action.  This file records the exact missing structure; no arbitrary
equivalence or complement block is instantiated.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure.EtaTensorBlockDetActual
open scoped TensorProduct

namespace LeanFormal.IUT.N8Closure.EtaTensorBinaryDecompositionActual

universe u

variable {p : Nat} [Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
  [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable (j : ι)

/-- Exact missing binary decomposition: complement B, linear equivalence, and
compatibility of the pure-tensor action with mult(g) (x) id. -/
structure TensorBinaryDecompositionData (p : Nat) [Fact p.Prime]
    (A : ι → Type) [∀ i, NormedField (A i)]
    [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
    (j : ι) (g : A j) where
  B : Type u
  [addB : AddCommGroup B]
  [moduleB : Module ℚ_[p] B]
  equiv : TensorBlock (p := p) A ≃ₗ[ℚ_[p]] TensorProduct ℚ_[p] (A j) B
  action_compatibility :
    ∀ x : TensorBlock (p := p) A,
      equiv (tensorAction (p := p) A j g x) =
        TensorProduct.map (LinearMap.mulLeft ℚ_[p] g) LinearMap.id (equiv x)

attribute [instance] TensorBinaryDecompositionData.addB TensorBinaryDecompositionData.moduleB

/-- Exact universally quantified missing decomposition theorem. -/
def MissingTensorBinaryDecompositionTheorem : Prop :=
  ∀ g : A j, ∃ _d : TensorBinaryDecompositionData.{u} p A j g, True

/-- Exact BPS determinant target. -/
def TensorDetNormTarget (g : A j) : Prop :=
  tensorDet (p := p) A j g =
    (Algebra.norm ℚ_[p] g) ^ (totalDim (p := p) A / factorDim (p := p) A j)

/-- The remaining gap in the BPS determinant route. -/
structure EtaTensorBinaryDecompositionGap (g : A j) where
  decomposition : TensorBinaryDecompositionData p A j g
  binary_det_norm :
    LinearMap.det
        (TensorProduct.map (LinearMap.mulLeft ℚ_[p] g) LinearMap.id :
          TensorProduct ℚ_[p] (A j) decomposition.B →ₗ[ℚ_[p]]
            TensorProduct ℚ_[p] (A j) decomposition.B) =
      (Algebra.norm ℚ_[p] g) ^
        (totalDim (p := p) A / factorDim (p := p) A j)

end LeanFormal.IUT.N8Closure.EtaTensorBinaryDecompositionActual
