import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-!
# ShehddQParameterConsumerActual — q-parameter Def 3.1(b) log bookkeeping consumer

STEP 0 prior-art (reuse only; A475 search: q-parameter assets found in tree):
* IUTIII/Corollary312/ArithmeticQPilotLogVolume.lean: qNorm_pos / qNorm_lt_one,
  localSignedLog / localLogMagnitude, localSignedLog_neg / localLogMagnitude_pos,
  abs_localSignedLog, exp_neg_localLogMagnitude, localLogMagnitude_pow,
  selectedLogMagnitude / selectedSignedLog and their positivity/negativity;
* IUTIII/Corollary312/ArithmeticQPilotBaseChange.lean: residueNormBase / qNorm
  base-change normalizations (nonempty place data).

This file exposes the Def 3.1(b) q-parameter log bookkeeping as consumer statements
(positive norm < 1, negative signed q-log, positive magnitude, exp/log inverse,
power scaling, finite weighted aggregation).  No new assumptions, no sorry/axiom; the
identification with all paper bad-reduction places stays out of tree scope (explicit
docstring of ArithmeticQPilotLogVolume).
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddQParameterConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace

variable {K : Type*} [Field K] [NumberField K]
variable {place : NumberField.FinitePlace K}

/-- **PROVED consumer:** a q-candidate at a finite place has positive norm below one,
negative signed q-log and positive log-magnitude (Def 3.1(b) local bookkeeping). -/
theorem qCandidate_log_summary (parameter : FinitePlaceQCandidate place) :
    0 < ‖parameter.q‖ ∧ ‖parameter.q‖ < 1 ∧
      localSignedLog parameter < 0 ∧ 0 < localLogMagnitude parameter :=
  ⟨qNorm_pos parameter, qNorm_lt_one parameter, localSignedLog_neg parameter,
    localLogMagnitude_pos parameter⟩

/-- **PROVED consumer:** the exponential of minus the log-magnitude is the norm, and
the absolute signed log is the magnitude. -/
theorem qCandidate_exp_and_abs (parameter : FinitePlaceQCandidate place) :
    Real.exp (-localLogMagnitude parameter) = ‖parameter.q‖ ∧
      |localSignedLog parameter| = localLogMagnitude parameter :=
  ⟨exp_neg_localLogMagnitude parameter, abs_localSignedLog parameter⟩

/-- **PROVED consumer:** positive powers scale the local log-magnitude linearly. -/
theorem qCandidate_pow_magnitude (parameter : FinitePlaceQCandidate place)
    (exponent : ℕ) (exponent_pos : 0 < exponent) :
    localLogMagnitude (parameter.pow exponent exponent_pos) =
      (exponent : ℝ) * localLogMagnitude parameter :=
  localLogMagnitude_pow parameter exponent exponent_pos

section Selected

variable (selectedPlaces : Finset (NumberField.FinitePlace K))
variable (parameters : (selectedPlace : selectedPlaces) →
  FinitePlaceQCandidate selectedPlace.val)
variable (weights : selectedPlaces → ℝ)

/-- **PROVED consumer:** a finite positive weighted aggregation over nonempty selected
places has positive log-magnitude and negative signed q-log. -/
theorem selected_q_log_summary (hne : selectedPlaces.Nonempty)
    (hw : ∀ selectedPlace, 0 < weights selectedPlace) :
    0 < selectedLogMagnitude selectedPlaces parameters weights ∧
      selectedSignedLog selectedPlaces parameters weights < 0 :=
  ⟨selectedLogMagnitude_pos selectedPlaces parameters weights hne hw,
    selectedSignedLog_neg selectedPlaces parameters weights hne hw⟩

end Selected

/-- Row record: reused q-parameter laws vs consumer statements. -/
def qParameterConsumerRows : List (String × String × String) :=
  [ ("local q norm/sign/magnitude laws", "REUSED PROVED", "ArithmeticQPilotLogVolume.qNorm_pos / qNorm_lt_one / localSignedLog_neg / localLogMagnitude_pos")
  , ("exp/abs/pow local laws", "REUSED PROVED", "exp_neg_localLogMagnitude / abs_localSignedLog / localLogMagnitude_pow")
  , ("finite weighted selected-places aggregation laws", "REUSED PROVED", "selectedLogMagnitude_pos / selectedSignedLog_neg")
  , ("q-parameter consumer summaries", "COMPOSED PROVED", "qCandidate_log_summary, qCandidate_exp_and_abs, qCandidate_pow_magnitude, selected_q_log_summary")
  , ("identification with all bad-reduction places / paper q-pilot volume", "REPO-CURRENT-LIMIT (tree docstring)", "ArithmeticQPilotLogVolume header: no Tate uniformization/normalization identification asserted") ]

theorem qParameterConsumerRows_length : qParameterConsumerRows.length = 5 := rfl

#check qCandidate_log_summary
#check qCandidate_exp_and_abs
#check qCandidate_pow_magnitude
#check selected_q_log_summary
#check qParameterConsumerRows_length

end LeanFormal.IUT.XiFPaper.ShehddQParameterConsumerActual
end
