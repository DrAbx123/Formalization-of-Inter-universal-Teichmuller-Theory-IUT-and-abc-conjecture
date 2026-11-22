import tmp.sheaf.xif.paper.Mzk1P3TensorCoreActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlockFields
/-! P3 (R3.1): block field-product decomposition map (no C3). -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3DomainDecompositionMapActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
theorem domainDecompositionMap (tuple : (i : ι) → V i) :
    ∃ (J : Type (max u v)) (_ : Fintype J) (E : J → Type (max u v))
      (_ : ∀ j, NontriviallyNormedField (E j))
      (_ : ∀ j, NormedAlgebra ℚ_[p] (E j))
      (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)),
      (∀ j, FiniteDimensional ℚ_[p] (E j)) ∧ Continuous e ∧ Continuous e.symm := by
  obtain ⟨J, hJ, E, hfield, halg, e, hprops⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  exact ⟨J, hJ, E, hfield, halg, e, (fun j => (hprops.1 j).1), hprops.2.1, hprops.2.2⟩
def fieldProductProjection
    {J : Type*} (E : J → Type*) (j : J) (x : (j : J) → E j) : E j := x j
theorem fieldProductProjection_apply
    {J : Type*} (E : J → Type*) (j : J) (x : (j : J) → E j) :
    fieldProductProjection E j x = x j := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P3DomainDecompositionMapActual
end