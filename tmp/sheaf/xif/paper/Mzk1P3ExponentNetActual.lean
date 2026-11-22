import tmp.sheaf.xif.paper.Mzk1P3TensorCoreActual
/-! P3 (R3.7): exact exponent and net quantity from the field decomposition. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P3ExponentNetActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
/-- Exact block exponent: the actual `Q_p`-dimension of the tensor block. -/
noncomputable def blockExponent (tuple : (i : ι) → V i) : Nat :=
  Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple)
/-- Net field-component exponent `Σ_j finrank E_j`. -/
noncomputable def exponentNet {J : Type*} [Fintype J] (E : J → Type*)
    [∀ j, AddCommGroup (E j)] [∀ j, Module ℚ_[p] (E j)] : Nat :=
  ∑ j, Module.finrank ℚ_[p] (E j)
/-- The net field-component exponent equals the exact block exponent. -/
theorem exponentNet_eq_blockExponent (tuple : (i : ι) → V i)
    {J : Type*} [Fintype J] (E : J → Type*)
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)]
    [∀ j, Module.Free ℚ_[p] (E j)] [∀ j, Module.Finite ℚ_[p] (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    exponentNet (p := p) E = blockExponent places tuple := by
  unfold exponentNet blockExponent
  exact (tensorCore_finrank_eq_sum places tuple E e).symm
end LeanFormal.IUT.XiFPaper.Mzk1P3ExponentNetActual
end