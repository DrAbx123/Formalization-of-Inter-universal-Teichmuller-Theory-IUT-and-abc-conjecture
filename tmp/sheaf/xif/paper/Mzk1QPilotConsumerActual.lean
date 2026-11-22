import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-!
# Mzk1QPilotConsumerActual — consumer theorems over the arithmetic q-pilot log-volume
assets (tree asset, OLEAN_FRESH). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {place : NumberField.FinitePlace K}

/-- Consumer: the q-candidate norm is positive. -/
theorem consumer_qNorm_pos (parameter : FinitePlaceQCandidate place) :
    0 < ‖parameter.q‖ :=
  qNorm_pos parameter

/-- Consumer: the q-candidate norm is less than one. -/
theorem consumer_qNorm_lt_one (parameter : FinitePlaceQCandidate place) :
    ‖parameter.q‖ < 1 :=
  qNorm_lt_one parameter

/-- Consumer: the signed local q-pilot log is negative. -/
theorem consumer_localSignedLog_neg (parameter : FinitePlaceQCandidate place) :
    localSignedLog parameter < 0 :=
  localSignedLog_neg parameter

/-- Consumer: the local log magnitude is positive. -/
theorem consumer_localLogMagnitude_pos (parameter : FinitePlaceQCandidate place) :
    0 < localLogMagnitude parameter :=
  localLogMagnitude_pos parameter

#check consumer_qNorm_pos
#check consumer_qNorm_lt_one
#check consumer_localSignedLog_neg
#check consumer_localLogMagnitude_pos

end LeanFormal.IUT.XiFPaper.Mzk1QPilotConsumerActual
end
