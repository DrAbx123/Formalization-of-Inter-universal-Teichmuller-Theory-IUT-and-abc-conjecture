import LeanFormal.IUT.Foundations.Geometry.TateUniformizationContract
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-!
# ShehddL02TateParameterChainActual — L0.2 Tate-parameter candidate chain

Region prerequisite for legacy-dag:l0.2-tate-parameter, combining compiled tree assets:
the actual Tate parameter unit (TateUniformizationContract) attached to a finite-place
q-candidate, together with the candidate's analytic norm/log facts
(ArithmeticQPilotLogVolume).  This is a genuine chain: the parameter unit is nontrivial and
the candidate q is contracting with negative signed log.

No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddL02TateParameterChainActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume

variable {K : Type*} [Field K] [NumberField K]
variable {place : NumberField.FinitePlace K}

/-- **PROVED chain:** a q-candidate at a finite place gives a nontrivial actual Tate
parameter unit, while the candidate q is positive, contracting, and has negative signed
local log. -/
theorem tateParameterCandidate_chain
    (parameter : FinitePlaceQCandidate place) :
    tateParameterUnit place parameter.q parameter.q_ne_zero ≠ 1 ∧
      0 < ‖parameter.q‖ ∧ ‖parameter.q‖ < 1 ∧
        localSignedLog parameter < 0 :=
  ⟨tateParameterUnit_ne_one place parameter.q parameter.q_ne_zero
      (FinitePlaceQCandidate.q_ne_one parameter),
    qNorm_pos parameter,
    qNorm_lt_one parameter,
    localSignedLog_neg parameter⟩

/-- **PROVED chain:** the candidate's positive power keeps the Tate-parameter unit
nontrivial and contracting (power candidate data + unit power law). -/
theorem tateParameterCandidate_pow_chain
    (parameter : FinitePlaceQCandidate place) (n : Nat) (hn : 0 < n) :
    tateParameterUnit place (parameter.q ^ n)
        (pow_ne_zero n parameter.q_ne_zero) =
      (tateParameterUnit place parameter.q parameter.q_ne_zero) ^ n ∧
      0 < ‖parameter.q ^ n‖ ∧ ‖parameter.q ^ n‖ < 1 :=
  ⟨tateParameterUnit_pow place parameter.q parameter.q_ne_zero n,
    ⟨norm_pos_iff.mpr (pow_ne_zero n parameter.q_ne_zero), by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) (qNorm_lt_one parameter)
        (Nat.pos_iff_ne_zero.mp hn)⟩⟩

end LeanFormal.IUT.XiFPaper.ShehddL02TateParameterChainActual
end
