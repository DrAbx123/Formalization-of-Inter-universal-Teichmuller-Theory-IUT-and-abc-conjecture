import LeanFormal.IUT.Foundations.Theta.OddTheta
import LeanFormal.IUT.Foundations.Theta.OddThetaNegativeDecay
import LeanFormal.IUT.Foundations.Theta.OddThetaNonvanishing

/-!
# ShehddOddThetaTermChainActual — odd theta backward-term and nonvanishing chain

New chain consequences of the compiled odd theta term/decay/nonvanishing laws: the
backward term formula, summability of the backward half, the vanishing-free point at a
square root of -1, and the exponent lower bound off {0,-1}.  No new assumptions, no
sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddOddThetaTermChainActual

open LeanFormal.IUT
open LeanFormal.IUT.Foundations.Theta

universe u

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- **PROVED chain:** backward theta terms are minus the forward terms of the inverse, with
the exponent/sign bookkeeping. -/
theorem oddThetaTerm_backward_chain (q U : L) (n : Nat) :
    oddThetaExponent (-((n : Int) + 1)) = oddThetaExponent (n : Int) ∧
      oddThetaSign (L := L) (-((n : Int) + 1)) =
        -oddThetaSign (L := L) (n : Int) ∧
        oddThetaTerm q U (-((n : Int) + 1)) =
          -oddThetaTerm q U⁻¹ (n : Int) := by
  refine ⟨oddThetaExponent_neg_succ n, oddThetaSign_neg_succ n, ?_⟩
  exact oddThetaTerm_neg_succ q U n

/-- **PROVED chain:** the backward half of the odd theta series is summable. -/
theorem oddTheta_backward_summable_chain (q U : L) (hU : U ≠ 0) (hq : ‖q‖ < 1) :
    Summable (fun n : Nat => oddThetaTerm q U (-(n : Int))) :=
  summable_oddThetaTerm_neg q U hU hq

/-- **PROVED chain:** at a square root of -1 the odd theta value does not vanish. -/
theorem oddTheta_nonvanishing_chain (q i : L) (hi : i ^ 2 = -1)
    (hq : ‖q‖ < 1) (hq_two : ‖q‖ < ‖(2 : L)‖) :
    oddTheta q i ≠ 0 :=
  oddTheta_ne_zero_at_i q i hi hq hq_two

/-- **PROVED chain:** off `{0,-1}` the theta exponent is at least one. -/
theorem oddThetaExponent_lower_bound_chain (n : Int)
    (hn : n ∉ ({0, -1} : Finset Int)) :
    1 ≤ oddThetaExponent n :=
  oddThetaExponent_one_le_of_not_mem n hn

end LeanFormal.IUT.XiFPaper.ShehddOddThetaTermChainActual
end
