import tmp.sheaf.xif.paper.Mzk1P7ThetaDegB2Actual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlockFields
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! P3/P0 tensor core: pure tensor content parameterized by `(p, places, tuple,
finite extensions E_i)`, independent of any `C3` inhabitant. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P7ThetaDegB2Actual

universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)

/-- Core field-product decomposition of the actual tensor tuple block. -/
theorem tensorCore_fieldProduct (tuple : (i : ι) → V i) :
    ∃ (J : Type (max u v)) (_ : Fintype J) (E : J → Type (max u v))
      (_ : ∀ j, NontriviallyNormedField (E j))
      (_ : ∀ j, NormedAlgebra ℚ_[p] (E j))
      (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)),
      (∀ j, FiniteDimensional ℚ_[p] (E j)) := by
  obtain ⟨J, hJ, E, hfield, halg, e, hprops⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  exact ⟨J, hJ, E, hfield, halg, e, fun j => (hprops.1 j).1⟩

/-- Core dimension-sum identity: block dimension = sum of component local degrees. -/
theorem tensorCore_finrank_eq_sum (tuple : (i : ι) → V i)
    {J : Type*} [Fintype J] (E : J → Type*)
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)]
    [∀ j, Module.Free ℚ_[p] (E j)] [∀ j, Module.Finite ℚ_[p] (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) =
      ∑ j, Module.finrank ℚ_[p] (E j) :=
  finrank_arithmeticTensorTupleBlock_eq_sum_fieldProduct places tuple E e


end LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreActual
end