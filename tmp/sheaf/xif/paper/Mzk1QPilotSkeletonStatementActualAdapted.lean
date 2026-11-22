import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-! Mainline: q-pilot skeleton statement (concrete tree facts bundled; real proofs). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotSkeletonStatementActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open NumberFieldFinitePlace

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {place : NumberField.FinitePlace K}

/-- q-pilot skeleton statement: positivity, q < 1 and negative signed log. -/
def QPilotSkeletonStatement (parameter : FinitePlaceQCandidate place) : Prop :=
  0 < ‖parameter.q‖ ∧ ‖parameter.q‖ < 1 ∧ localSignedLog parameter < 0

theorem qPilotSkeletonStatement_proved (parameter : FinitePlaceQCandidate place) :
    QPilotSkeletonStatement parameter :=
  ⟨qNorm_pos parameter, qNorm_lt_one parameter, localSignedLog_neg parameter⟩

theorem qPilotSkeleton_q_ne_zero (parameter : FinitePlaceQCandidate place) :
    parameter.q ≠ 0 :=
  parameter.q_ne_zero

theorem qPilotSkeleton_qNorm_lt_one (parameter : FinitePlaceQCandidate place) :
    ‖parameter.q‖ < 1 :=
  qNorm_lt_one parameter

end LeanFormal.IUT.XiFPaper.Mzk1QPilotSkeletonStatementActualAdapted