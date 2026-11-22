import LeanFormal/IUT/IUTIII/Corollary312/ArithmeticQPilotLogVolume

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1QPilotNormPackageActual — A479 real consumer theorems (q-pilot norm/log)

New conclusions combining the existing donors of
`ArithmeticQPilotLogVolume.lean` (:25/30/42/46/50/54):

1. `qpilot_norm_package`: the q-candidate norm lies in (0,1), its signed
   logarithm is negative and its log-magnitude is positive — all four
   conclusions jointly;
2. `localLogMagnitude_eq_neg_signed`: the log-magnitude is the negative of the
   signed logarithm (reverse orientation of :50);
3. `qpilot_abs_log_chain`: the absolute signed log equals the magnitude and the
   signed log equals the negative magnitude jointly.

No sorry/axioms; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotNormPackageActual

open LeanFormal.IUT
open LeanFormal.IUT.ArithmeticQPilotLogVolume

/-- Joint q-pilot norm/log package for an actual finite-place q-candidate. -/
theorem qpilot_norm_package {K : Type*} [Field K] [NumberField K]
    {place : NumberField.FinitePlace K}
    (parameter : FinitePlaceQCandidate place) :
    0 < ‖parameter.q‖ ∧ ‖parameter.q‖ < 1 ∧
      localSignedLog parameter < 0 ∧ 0 < localLogMagnitude parameter :=
  ⟨qNorm_pos parameter, qNorm_lt_one parameter,
   localSignedLog_neg parameter, localLogMagnitude_pos parameter⟩

/-- The log-magnitude is the negative of the signed logarithm. -/
theorem localLogMagnitude_eq_neg_signed {K : Type*} [Field K] [NumberField K]
    {place : NumberField.FinitePlace K}
    (parameter : FinitePlaceQCandidate place) :
    localLogMagnitude parameter = -localSignedLog parameter := by
  rw [localSignedLog_eq_neg_magnitude parameter]
  ring

/-- Chain form: absolute signed log = magnitude and signed log = -magnitude. -/
theorem qpilot_abs_log_chain {K : Type*} [Field K] [NumberField K]
    {place : NumberField.FinitePlace K}
    (parameter : FinitePlaceQCandidate place) :
    |localSignedLog parameter| = localLogMagnitude parameter ∧
      localSignedLog parameter = -localLogMagnitude parameter :=
  ⟨abs_localSignedLog parameter, localSignedLog_eq_neg_magnitude parameter⟩

#check qpilot_norm_package
#check localLogMagnitude_eq_neg_signed

end LeanFormal.IUT.XiFPaper.Mzk1QPilotNormPackageActual
end