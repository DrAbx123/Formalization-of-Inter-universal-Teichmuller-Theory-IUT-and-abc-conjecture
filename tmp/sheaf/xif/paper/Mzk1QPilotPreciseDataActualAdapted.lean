import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-! Mainline: q-pilot precise construction data (real bundling of tree candidate facts). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotPreciseDataActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open NumberFieldFinitePlace

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {place : NumberField.FinitePlace K}

/-- Precise q-pilot data: a q-candidate with q≠0, norm in (0,1), and signed log = -magnitude. -/
structure QPilotPreciseData (parameter : FinitePlaceQCandidate place) : Prop where
  q_ne_zero : parameter.q ≠ 0
  qNorm_pos : 0 < ‖parameter.q‖
  qNorm_lt_one : ‖parameter.q‖ < 1
  signedLog_formula :
    localSignedLog parameter = -localLogMagnitude parameter

/-- Every q-candidate carries the precise q-pilot data (real proofs from tree facts). -/
theorem qPilotPreciseData_of_candidate (parameter : FinitePlaceQCandidate place) :
    QPilotPreciseData parameter :=
  ⟨parameter.q_ne_zero, qNorm_pos parameter, qNorm_lt_one parameter,
    localSignedLog_eq_neg_magnitude parameter⟩

theorem qPilotPreciseData_nonempty (parameter : FinitePlaceQCandidate place) :
    Nonempty (QPilotPreciseData parameter) :=
  ⟨qPilotPreciseData_of_candidate parameter⟩

end LeanFormal.IUT.XiFPaper.Mzk1QPilotPreciseDataActualAdapted