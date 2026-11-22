import tmp.sheaf.xif.paper.Mzk1P3TensorCoreActual
import tmp.sheaf.xif.paper.Mzk1P6StepVESupportFinalAct
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULFieldProduct2Actual
open LeanFormal.IUT LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
/-- Explicit finite-étale field product of the actual base completion tensor block. -/
theorem ulFieldProduct (tuple : (i : ι) → V i) :
    ∃ (J : Type (max u v)) (hJ : Fintype J) (E : J → Type (max u v))
      (_ : ∀ j, NontriviallyNormedField (E j))
      (_ : ∀ j, NormedAlgebra ℚ_[p] (E j))
      (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
      (_ : ∀ j, FiniteDimensional ℚ_[p] (E j)),
      Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) =
        ∑ j, Module.finrank ℚ_[p] (E j) :=
  Mzk1P6StepVESupportFinalAct.stepV_fieldProduct_finrank places tuple
#print axioms ulFieldProduct
end LeanFormal.IUT.XiFPaper.Mzk1ULFieldProduct2Actual
end