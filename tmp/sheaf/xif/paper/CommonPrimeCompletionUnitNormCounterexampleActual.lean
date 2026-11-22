import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import Mathlib.Analysis.Normed.Field.Basic

/-!
# CommonPrimeCompletion units need not have norm one

The proposed lemma

  forall u : (CommonPrimeCompletion place)^x, ||u|| = 1

is false.  CommonPrimeCompletion is a nontrivially normed field, so it has an
element x with 0 < ||x|| < 1.  Since a field is a division ring, x is a unit, and
its norm is not one.  The integral units (Integers K)^x do have norm one, but
the full completion unit group does not.

This is an actual counterexample, not a fake decomposition.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.CommonPrimeCompletionUnitNormCounterexampleActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- There is a unit of CommonPrimeCompletion with norm not equal to one. -/
theorem exists_commonPrimeCompletion_unit_norm_ne_one :
    ∃ u : (CommonPrimeCompletion place)ˣ,
      ‖(u : CommonPrimeCompletion place)‖ ≠ 1 := by
  rcases NormedField.exists_norm_lt_one (NormalizedCompletion place.val) with ⟨y, hy0, hy1⟩
  let x : CommonPrimeCompletion place := y
  have hx0 : 0 < ‖x‖ := hy0
  have hx1 : ‖x‖ < 1 := hy1
  have hxne : x ≠ 0 := norm_pos_iff.mp hx0
  refine ⟨Units.mk0 x hxne, ?_⟩
  simpa using ne_of_lt hx1

/-- The universal unit norm-one assertion for CommonPrimeCompletion is false. -/
theorem not_forall_commonPrimeCompletion_unit_norm_one :
    ¬ ∀ u : (CommonPrimeCompletion place)ˣ,
      ‖(u : CommonPrimeCompletion place)‖ = 1 := by
  intro h
  rcases exists_commonPrimeCompletion_unit_norm_ne_one place with ⟨u, hu⟩
  exact hu (h u)

/-- The same counterexample stated as: there exists a nonzero element whose
norm is not one, hence a completion unit. -/
theorem exists_commonPrimeCompletion_norm_ne_one :
    ∃ x : CommonPrimeCompletion place, x ≠ 0 ∧ ‖x‖ ≠ 1 := by
  rcases exists_commonPrimeCompletion_unit_norm_ne_one place with ⟨u, hu⟩
  exact ⟨(u : CommonPrimeCompletion place), Units.ne_zero u, hu⟩

end LeanFormal.IUT.XiFPaper.CommonPrimeCompletionUnitNormCounterexampleActual
end
