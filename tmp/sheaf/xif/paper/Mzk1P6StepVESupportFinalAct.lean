import tmp.sheaf.xif.paper.Mzk1TensorCoreWitnessActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6StepVESupportFinalAct
open LeanFormal.IUT LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
/-- P6 StepV: the actual tensor block has a field product decomposition whose
finrank is the sum of the factor finranks. -/
theorem stepV_fieldProduct_finrank (tuple : (i : ι) → V i) :
    ∃ (J : Type (max u v)) (hJ : Fintype J) (E : J → Type (max u v))
      (_ : ∀ j, NontriviallyNormedField (E j))
      (_ : ∀ j, NormedAlgebra ℚ_[p] (E j))
      (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
      (_ : ∀ j, FiniteDimensional ℚ_[p] (E j)),
      Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) =
        ∑ j, Module.finrank ℚ_[p] (E j) := by
  obtain ⟨J, hJ, E, hfield, halg, e, hfin⟩ := tensorCore_fieldProduct places tuple
  letI : Fintype J := hJ
  letI : ∀ j, NontriviallyNormedField (E j) := hfield
  letI : ∀ j, NormedAlgebra ℚ_[p] (E j) := halg
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := hfin
  exact ⟨J, hJ, E, hfield, halg, e, hfin,
    tensorCore_finrank_eq_sum places tuple E e⟩
#print axioms stepV_fieldProduct_finrank
end LeanFormal.IUT.XiFPaper.Mzk1P6StepVESupportFinalAct
end