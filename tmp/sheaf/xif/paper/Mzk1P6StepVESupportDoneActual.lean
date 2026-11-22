import tmp.sheaf.xif.paper.Mzk1TensorCoreWitnessActual
import tmp.sheaf.xif.paper.Mzk1BoxStepVAverageActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6StepVESupportDoneActual
open LeanFormal.IUT LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1TensorCoreWitnessActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
/-- P6 StepV: actual field-product decomposition of the tensor block,-
from `tensorCore_fieldProduct`. -/
theorem stepV_fieldProduct (tuple : (i : ι) → V i) :
    ∃ (J : Type (max u v)) (_ : Fintype J) (E : J → Type (max u v))
      (_ : ∀ j, NontriviallyNormedField (E j))
      (_ : ∀ j, NormedAlgebra ℚ_[p] (E j))
      (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)),
      (∀ j, FiniteDimensional ℚ_[p] (E j)) :=
  tensorCore_fieldProduct places tuple
/-- P6 StepV: actual witness structure carrying `e`. -/
noncomputable def stepVWitness (tuple : (i : ι) → V i) :
    TensorCoreWitness places tuple :=
  tensorCoreWitness places tuple
/-- P6 StepV: finrank of the actual tensor block is the sum of local factor degrees. -/
theorem stepV_finrank_eq_sum (tuple : (i : ι) → V i) :
    Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) =
      ∑ j, Module.finrank ℚ_[p] ((stepVWitness places tuple).E j) := by
  let W := stepVWitness places tuple
  letI : Fintype W.J := W.fintype
  letI : ∀ j, NontriviallyNormedField (W.E j) := W.field
  letI : ∀ j, NormedAlgebra ℚ_[p] (W.E j) := W.alg
  letI : ∀ j, FiniteDimensional ℚ_[p] (W.E j) := W.finite
  exact tensorCore_finrank_eq_sum places tuple W.E W.equiv
#print axioms stepV_fieldProduct
#print axioms stepV_finrank_eq_sum
end LeanFormal.IUT.XiFPaper.Mzk1P6StepVESupportDoneActual
end