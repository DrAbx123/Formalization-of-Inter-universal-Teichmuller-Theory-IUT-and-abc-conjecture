import tmp.sheaf.xif.paper.Mzk1P3TensorCoreActual
import tmp.sheaf.xif.paper.Mzk1P2NativeBlockAlignmentActual
import Mathlib.Tactic

/-! # P2: tensor field-product det factor

B2 gives a Qp-algebra equivalence from the actual tensor block to a finite
product of normed fields.  This file records the field-product equivalence,
the dimension-sum identity, and the resulting scalar p-degree determinant
factor.

Exact GAP: the p-adic Haar scaling law for an arbitrary linear equivalence
(measure transport = norm of determinant) is not available in the tree.  Only
the scalar p-scaling law is available, so the arbitrary det factor is not
asserted.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P2TensorDetFactorActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1P2NativeBlockAlignmentActual
open MeasureTheory

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι -> Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)

/-- Actual B2 field-product equivalence of the tensor tuple block. -/
theorem p2TensorFieldProduct (tuple : (i : ι) -> V i) :
    ∃ (J : Type (max u v)) (_ : Fintype J) (E : J -> Type (max u v))
      (_ : ∀ j, NontriviallyNormedField (E j))
      (_ : ∀ j, NormedAlgebra ℚ_[p] (E j))
      (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) -> E j)),
      (∀ j, FiniteDimensional ℚ_[p] (E j)) :=
  tensorCore_fieldProduct places tuple

/-- Dimension-sum determinant degree identity. -/
theorem p2TensorFinrank_eq_sum (tuple : (i : ι) -> V i)
    {J : Type*} [Fintype J] (E : J -> Type*)
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)]
    [∀ j, Module.Free ℚ_[p] (E j)] [∀ j, Module.Finite ℚ_[p] (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) -> E j)) :
    Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) =
      ∑ j, Module.finrank ℚ_[p] (E j) :=
  tensorCore_finrank_eq_sum places tuple E e

/-- Scalar p-degree det factor of the tensor block. -/
noncomputable def p2TensorScalarDetFactor
    (tuple : (i : ι) -> V i) : Real :=
  (p : Real) ^ Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple)

theorem p2TensorScalarDetFactor_pos (tuple : (i : ι) -> V i) :
    0 < p2TensorScalarDetFactor (p := p) places tuple := by
  unfold p2TensorScalarDetFactor
  exact pow_pos (Nat.cast_pos.mpr (Fact.out : Nat.Prime p).pos) _

/-- Exact missing p-adic Haar det law for an arbitrary field-product algebra
equivalence. -/
def p2TensorHaarDetTransportMissing : List String :=
  [ "p-adic Haar scaling under arbitrary continuous linear equivalence (norm-of-det law)",
    "determinant of the B2 field-product algebra equivalence in chosen bases",
    "log-volume transport from the native tensor block to the product carrier" ]

theorem p2TensorHaarDetTransportMissing_length :
    p2TensorHaarDetTransportMissing.length = 3 := rfl

#check p2TensorFieldProduct
#check p2TensorFinrank_eq_sum
#check p2TensorScalarDetFactor
#check p2TensorScalarDetFactor_pos
#check p2TensorHaarDetTransportMissing
end LeanFormal.IUT.XiFPaper.Mzk1P2TensorDetFactorActual
end
