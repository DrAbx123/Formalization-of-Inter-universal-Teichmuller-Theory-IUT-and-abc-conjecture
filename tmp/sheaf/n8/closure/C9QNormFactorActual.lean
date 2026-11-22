import tmp.sheaf.n8.closure.C7MassFormulaZeroSorry
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-!
# C9 canonical/normalized q norm factor

E15 asks for the packaged q-factor

  localSignedLog(qCandidate S) = d S * Real.log ||qUnit S||.

The canonical side is actual: `localSignedLog` is the canonical completion
log norm, and `logNorm_eq_absNorm_mul` computes it from the q-candidate
valuation exponent.  The normalized side is the spectral norm on
`CommonPrimeCompletion`; the general normalized/canonical power comparison is
the exact residual recorded below (its production source lemmas are not
available as oleans in the current tree).  No axiom or sorry is introduced. -/

noncomputable section
set_option maxHeartbeats 4000000
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.N8Closure.C9QNormFactorActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.ArithmeticQPilotLogVolume

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

/-- The canonical q log, equal to `localSignedLog` of the paper q candidate. -/
noncomputable def canonicalQLog : ℝ :=
  Real.log ‖(qCandidate S).q‖

/-- The normalized q log: the actual PaperP6 `log ||qUnit||`. -/
noncomputable def normalizedQLog : ℝ :=
  Real.log ‖(qUnit S : PaperKf S)‖

theorem canonicalQLog_eq_localSignedLog :
    canonicalQLog S = localSignedLog (qCandidate S) := rfl

theorem normalizedQLog_eq_qLog :
    normalizedQLog S = Real.log ‖(qUnit S : PaperKf S)‖ := rfl

/-- The paper q unit is the q candidate at the paper place. -/
theorem qUnit_coe_eq_qCandidate :
    (qUnit S : PaperKf S) = ((qCandidate S).q : PaperKf S) := by
  rw [qUnit_coe]
  rfl

theorem qCandidate_absNorm_gt_one :
    1 < (Ideal.absNorm (pF S).maximalIdeal.asIdeal : ℝ) :=
  by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (pF S).maximalIdeal

/-- Canonical q log from the actual q-candidate valuation exponent. -/
theorem canonicalQLog_eq_neg_exponent_mul_log_absNorm :
    canonicalQLog S =
      -((qCandidate S).exponent : ℝ) *
        Real.log (Ideal.absNorm (pF S).maximalIdeal.asIdeal : ℝ) := by
  have hq : (qCandidate S).q ≠ 0 := (qCandidate S).q_ne_zero
  have hlog := NumberFieldFinitePlace.logNorm_eq_absNorm_mul (pF S)
    (qCandidate S).q hq
  have hexp :
      Multiplicative.toAdd (WithZero.unzero
        (valuation_ne_zero_of_ne_zero (pF S) (qCandidate S).q hq)) =
        -((qCandidate S).exponent : ℤ) := by
    unfold FinitePlaceQCandidate.exponent
    ring
  unfold canonicalQLog
  rw [hlog, hexp]
  push_cast
  ring

/-- Exact normalized/canonical q comparison: the missing normalized-norm
formula specialized to the q candidate. -/
def NormalizedCanonicalQComparison : Prop :=
  normalizedQLog S =
    -((qCandidate S).exponent : ℝ) *
        Real.log (Ideal.absNorm (pF S).maximalIdeal.asIdeal : ℝ) /
      (C7QPilotMassActual.d S : ℝ)

/-- The E15 factor statement. -/
def QNormFactor : Prop :=
  localSignedLog (qCandidate S) =
    (C7QPilotMassActual.d S : ℝ) * normalizedQLog S

theorem d_pos_real : (0 : ℝ) < (C7QPilotMassActual.d S : ℝ) :=
  by exact_mod_cast C7QPilotMassActual.d_pos S

theorem d_ne_zero_real : (C7QPilotMassActual.d S : ℝ) ≠ 0 := (d_pos_real S).ne'

/-- Exact equivalence: E15 is equivalent to the missing normalized-norm
formula at the q candidate.  The canonical side has been eliminated using the
actual canonical log formula. -/
theorem qNormFactor_iff_normalizedCanonicalQComparison :
    QNormFactor S ↔ NormalizedCanonicalQComparison S := by
  constructor
  · intro h
    unfold QNormFactor at h
    unfold NormalizedCanonicalQComparison
    rw [← canonicalQLog_eq_localSignedLog S,
      canonicalQLog_eq_neg_exponent_mul_log_absNorm S] at h
    rw [h]
    field_simp [d_ne_zero_real S]
  · intro h
    unfold NormalizedCanonicalQComparison at h
    unfold QNormFactor
    rw [← canonicalQLog_eq_localSignedLog S,
      canonicalQLog_eq_neg_exponent_mul_log_absNorm S]
    rw [h]
    field_simp [d_ne_zero_real S]

/-- Conditional E15 theorem: the factor follows from the exact normalized
formula.  This is the strongest actual packaging available without asserting
the missing normalized-norm comparison. -/
theorem qNormFactor_of_normalizedCanonicalQComparison
    (h : NormalizedCanonicalQComparison S) : QNormFactor S :=
  (qNormFactor_iff_normalizedCanonicalQComparison S).mpr h

/-- Exact gap: the normalized spectral norm formula at the q candidate is not
available from the current compiled API. -/
def QNormFactorGap : Prop := NormalizedCanonicalQComparison S

theorem qNormFactorGap_iff : QNormFactorGap S ↔ NormalizedCanonicalQComparison S :=
  Iff.rfl

end LeanFormal.IUT.N8Closure.C9QNormFactorActual

end