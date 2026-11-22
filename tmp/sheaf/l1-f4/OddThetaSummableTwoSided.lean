import OddThetaSummable
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

noncomputable section

namespace LeanFormal.IUT.Foundations.Theta

universe u

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- The full two-sided odd theta series is summable, combining the forward half
with the negative half. -/
theorem summable_oddThetaTerm (q U : L) (hU : U ≠ 0) (hq : ‖q‖ < 1) :
    Summable (fun n : ℤ => oddThetaTerm q U n) := by
  refine Summable.of_nat_of_neg_add_one (f := fun n : ℤ => oddThetaTerm q U n) ?_ ?_
  · exact summable_oddThetaTerm_nat q U hU hq
  · simpa [Int.cast_add, Int.cast_one, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using summable_oddThetaTerm_neg_nat q U hU hq

end LeanFormal.IUT.Foundations.Theta
