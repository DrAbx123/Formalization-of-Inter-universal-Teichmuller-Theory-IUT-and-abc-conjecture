import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-!
# Mzk1QPilotLogExpActual — derived exp/log laws for the arithmetic q-pilot log-volume
(new theorems from existing tree asset). No copies/bookkeeping, no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotLogExpActual

open LeanFormal.IUT
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {place : NumberField.FinitePlace K}

/-- The q-candidate norm lies in (0,1). -/
theorem qNorm_mem (parameter : FinitePlaceQCandidate place) :
    ‖parameter.q‖ ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨qNorm_pos parameter, qNorm_lt_one parameter⟩

/-- Exponentiating the signed q-log recovers the completed q-norm. -/
theorem exp_localSignedLog (parameter : FinitePlaceQCandidate place) :
    Real.exp (localSignedLog parameter) = ‖parameter.q‖ := by
  rw [localSignedLog, Real.exp_log (qNorm_pos parameter)]

/-- The log of the exponential magnitude is the magnitude itself. -/
theorem log_exp_localLogMagnitude (parameter : FinitePlaceQCandidate place) :
    Real.log (Real.exp (localLogMagnitude parameter)) = localLogMagnitude parameter :=
  Real.log_exp _

/-- The magnitude is the negative of the log of the q-norm. -/
theorem localLogMagnitude_eq_neg_log (parameter : FinitePlaceQCandidate place) :
    localLogMagnitude parameter = -Real.log ‖parameter.q‖ := rfl

#check qNorm_mem
#check exp_localSignedLog
#check log_exp_localLogMagnitude
#check localLogMagnitude_eq_neg_log

end LeanFormal.IUT.XiFPaper.Mzk1QPilotLogExpActual
end
