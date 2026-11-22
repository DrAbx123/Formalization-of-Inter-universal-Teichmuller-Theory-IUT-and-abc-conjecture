import LeanFormal.IUT.IUTIII.Corollary312.TateQPilotJComparison

/-!
# ShehddQPilotLogVolumeSummaryActualAdapted — q-pilot / Tate j-invariant log-volume consumer

STEP 0 prior-art (reuse only): IUTIII/Corollary312/TateQPilotJComparison.lean proves
* qPilotLogVolume l = -log ||q l|| = log l.value and qPilotLogVolume l > 0;
* tateJInvariantLogVolume l = log ||j|| = log l.value = qPilotLogVolume l;
* tateJInvariantLogVolume l + log ||q l|| = 0 and ||j|| * ||q|| = 1.

This file composes those PROVED facts into consumer-facing summary theorems for the
IUT III Cor 3.12 q-pilot normalized log-volume (the `-|log(q)|` side).  No new
assumptions, no sorry/axiom; the general Theta-pilot/log-volume objects remain NAMED
elsewhere (iut-skeleton, e-deep, AbsTopIII nodes).
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddQPilotLogVolumeSummaryActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.TateCurvePadic

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

/-- **PROVED composition:** the q-pilot logarithmic volume is positive, equals
`log l.value`, coincides with the Tate j-invariant logarithmic volume, and its
additive comparison with `log ||q l||` vanishes. -/
theorem qPilotLogVolume_summary :
    0 < qPilotLogVolume l ∧ qPilotLogVolume l = Real.log (l.value : ℝ) ∧
      tateJInvariantLogVolume l = qPilotLogVolume l ∧
        tateJInvariantLogVolume l + Real.log ‖q l‖ = 0 :=
  ⟨qPilotLogVolume_pos l, qPilotLogVolume_eq_log_prime l,
    tateJInvariantLogVolume_eq_qPilotLogVolume l,
    tateJInvariantLogVolume_add_log_q_norm l⟩

/-- **PROVED composition:** the Tate j-invariant logarithmic volume is positive and
equals the q-pilot logarithmic volume. -/
theorem tateJInvariantLogVolume_summary :
    0 < tateJInvariantLogVolume l ∧
      tateJInvariantLogVolume l = qPilotLogVolume l :=
  ⟨tateJInvariantLogVolume_pos l,
    tateJInvariantLogVolume_eq_qPilotLogVolume l⟩

/-- **PROVED composition:** the multiplicative norm comparison `||j|| * ||q|| = 1`
in the form consumed by the q-pilot log-volume normalization. -/
theorem qPilot_norm_mul_j_norm_one :
    ‖tateJInvariant l‖ * ‖q l‖ = 1 := tateJInvariant_norm_mul_q_norm_one l

/-- Row record: reused Tate comparison facts vs composed summaries. -/
def qPilotLogVolumeRows : List (String × String × String) :=
  [ ("qPilotLogVolume = -log ||q|| = log l.value, positive", "REUSED PROVED", "TateQPilotJComparison.qPilotLogVolume_pos / _eq_log_prime")
  , ("tateJInvariantLogVolume = qPilotLogVolume", "REUSED PROVED", "TateQPilotJComparison.tateJInvariantLogVolume_eq_qPilotLogVolume")
  , ("additive log comparison = 0; multiplicative norm = 1", "REUSED PROVED", "tateJInvariantLogVolume_add_log_q_norm / tateJInvariant_norm_mul_q_norm_one")
  , ("combined q-pilot log-volume summary", "COMPOSED PROVED", "qPilotLogVolume_summary, tateJInvariantLogVolume_summary, qPilot_norm_mul_j_norm_one")
  , ("general Theta-pilot log-volume / holomorphic hull objects", "NAMED elsewhere", "iut-skeleton, e-deep, AbsTopIII nodes; see coord/SURVEY-shehdd.md") ]

theorem qPilotLogVolumeRows_length : qPilotLogVolumeRows.length = 5 := rfl

#check qPilotLogVolume_summary
#check tateJInvariantLogVolume_summary
#check qPilot_norm_mul_j_norm_one
#check qPilotLogVolumeRows_length

end LeanFormal.IUT.XiFPaper.ShehddQPilotLogVolumeSummaryActualAdapted
end
