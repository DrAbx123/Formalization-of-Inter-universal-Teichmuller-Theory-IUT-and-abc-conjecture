import tmp.sheaf.n8.closure.EtaFPlaceComparisonProof

/-!
# Eta F-place corrected signed comparison

The raw normalized equality is false because qPilotProcessionNormalizedVolume is
negative and fPlaceLogVolume is nonnegative.  The corrected sign convention is

  EtaFPlaceSignedComparisonTarget X :
    fPlaceLogVolume X = -fPlaceNormalizedQVolume X.

This is the positive magnitude comparison, not an arbitrary sign choice: the
production identity fPlaceNormalizedQVolume = qPilotSignedLog and the actual
qPilotLogMagnitude give -qPilotSignedLog = qPilotLogMagnitude.

We derive the exact criterion

  fPlaceVolumeIndex X = Real.exp (qPilotLogMagnitude X)

and show the comparison is false at volume index 1.  The criterion remains an
exact gap; no arbitrary normalization or equality is assumed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaFPlaceSignedComparison

open scoped Padic

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open LeanFormal.IUT.N8Closure.EtaFPlaceComparisonProof
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace

variable {l : PrimeGeFive}
variable {X : N8NativeInput l}

/-- Corrected signed comparison target: the positive F-shell log-volume equals
the negative of the production normalized q volume. -/
def EtaFPlaceSignedComparisonTarget (X : N8NativeInput l) : Prop :=
  fPlaceLogVolume X = -fPlaceNormalizedQVolume X

/-- Production identity: negative normalized q volume is the actual q
log-magnitude. -/
theorem neg_fPlaceNormalizedQVolume_eq_magnitude (X : N8NativeInput l) :
    -fPlaceNormalizedQVolume X = qPilotLogMagnitude X := by
  rw [fPlaceNormalizedQVolume_eq_signedLog]
  rw [qPilotLogMagnitude, qPilotSignedLog]
  rw [ArithmeticQPilotLogVolume.localLogMagnitude,
    ArithmeticQPilotLogVolume.localSignedLog]

/-- Equivalent absolute-value form. -/
theorem signedComparison_iff_abs (X : N8NativeInput l) :
    EtaFPlaceSignedComparisonTarget X ↔
      fPlaceLogVolume X = |fPlaceNormalizedQVolume X| := by
  rw [EtaFPlaceSignedComparisonTarget, abs_of_neg (fPlaceNormalizedQVolume_negative X)]

/-- Exact arithmetic criterion: the corrected comparison holds iff the actual
production volume index is exp of the actual q log-magnitude. -/
theorem signedComparison_iff_index_exp_magnitude (X : N8NativeInput l) :
    EtaFPlaceSignedComparisonTarget X ↔
      fPlaceVolumeIndex X = Real.exp (qPilotLogMagnitude X) := by
  constructor
  · intro h
    have hlog : Real.log (fPlaceVolumeIndex X : Real) =
        qPilotLogMagnitude X := by
      rw [← fPlaceLogVolume_eq_log_index X]
      rw [EtaFPlaceSignedComparisonTarget] at h
      rw [h, neg_fPlaceNormalizedQVolume_eq_magnitude]
    have hpos : (0 : Real) < fPlaceVolumeIndex X := by
      exact_mod_cast (fPlaceVolumeConsumer X).index_pos
    have hexp := congrArg Real.exp hlog
    rw [Real.exp_log hpos] at hexp
    exact hexp
  · intro h
    have hlog : Real.log (fPlaceVolumeIndex X : Real) =
        qPilotLogMagnitude X := by
      rw [h, Real.log_exp]
    rw [EtaFPlaceSignedComparisonTarget]
    rw [fPlaceLogVolume_eq_log_index X, hlog,
      neg_fPlaceNormalizedQVolume_eq_magnitude X]

/-- The corrected comparison is not automatic: at volume index 1 it is false,
because the q log-magnitude is strictly positive. -/
theorem signedComparison_false_of_index_one
    (X : N8NativeInput l)
    (h : fPlaceVolumeIndex X = 1) :
    ¬ EtaFPlaceSignedComparisonTarget X := by
  intro htarget
  have hlog : fPlaceLogVolume X = 0 := by
    rw [fPlaceLogVolume, h]
    norm_num
  have hmagnitude_pos : 0 < qPilotLogMagnitude X :=
    ArithmeticQPilotLogVolume.localLogMagnitude_pos (nativeQ X)
  have hneg := neg_fPlaceNormalizedQVolume_eq_magnitude X
  rw [EtaFPlaceSignedComparisonTarget] at htarget
  rw [hlog] at htarget
  rw [← hneg] at hmagnitude_pos
  linarith

end LeanFormal.IUT.N8Closure.EtaFPlaceSignedComparison
