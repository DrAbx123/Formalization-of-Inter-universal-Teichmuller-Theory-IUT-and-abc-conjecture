import tmp.sheaf.n8.closure.O2ConstructedIdentification
import tmp.sheaf.n8.closure.EtaFPlaceSignedComparison
import Mathlib

/-!
# O2 corrected volume-index normalization

The naive identification is false.  The corrected target is stated with the
actual q pilot inverse:

  O2CorrectedVolumeIdentification X :
    ofAdd (etaRssAtFPlace.logVolume) = (etaPilot X)⁻¹.

This is proved equivalent to the actual signed F-place comparison and to the
exact corrected volume-index condition

  fPlaceVolumeIndex X = exp (qPilotLogMagnitude X).

At volume-index 1 the corrected target is still false, because the corrected
index exp (qPilotLogMagnitude) is strictly greater than 1.  No arbitrary sign
or arbitrary index is used.
-/

noncomputable section

namespace ABCBridge.N8.O2CorrectedVolumeIndex

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open LeanFormal.IUT.N8Closure.EtaFPlaceComparisonProof
open LeanFormal.IUT.N8Closure.EtaFPlaceSignedComparison
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual
open ABCBridge.N8.O2ConstructedIdentification

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Corrected volume-index normalization from actual q data. -/
def O2CorrectedVolumeIndex : ℝ :=
  Real.exp (qPilotLogMagnitude X)

/-- Corrected O2 identification with the actual q pilot inverse. -/
def O2CorrectedVolumeIdentification : Prop :=
  Multiplicative.ofAdd (etaRssAtFPlace (X := X)).logVolume = (etaPilot X)⁻¹

/-- The corrected identification is exactly the actual signed F-place
comparison. -/
theorem o2Corrected_iff_signed :
    O2CorrectedVolumeIdentification X ↔ EtaFPlaceSignedComparisonTarget X := by
  constructor
  · intro h
    have hlog := congrArg Multiplicative.toAdd h
    have hleft : Multiplicative.toAdd
        (Multiplicative.ofAdd (etaRssAtFPlace (X := X)).logVolume) =
        (etaRssAtFPlace (X := X)).logVolume := rfl
    have hinv : Multiplicative.toAdd ((etaPilot X)⁻¹) = qPilotLogMagnitude X := by
      have hp : etaPilot X = Multiplicative.ofAdd (qPilotSignedLog X) := by
        simp [etaPilot, qPilotKummerRelativeVolume_eq]
      have hmag : qPilotLogMagnitude X = -qPilotSignedLog X := rfl
      rw [hp, hmag]
      simp
    rw [hleft, hinv] at hlog
    rw [EtaFPlaceSignedComparisonTarget]
    rw [← etaRssAtFPlace_logVolume_eq (X := X)]
    rw [neg_fPlaceNormalizedQVolume_eq_magnitude]
    exact hlog
  · intro h
    exact corrected_identification_of_signedComparison X h

/-- Exact corrected volume-index criterion. -/
theorem o2Corrected_iff_index :
    O2CorrectedVolumeIdentification X ↔
      (fPlaceVolumeIndex X : ℝ) = O2CorrectedVolumeIndex X := by
  rw [o2Corrected_iff_signed]
  exact signedComparison_iff_index_exp_magnitude X

/-- The corrected index is strictly greater than 1. -/
theorem one_lt_O2CorrectedVolumeIndex :
    (1 : ℝ) < O2CorrectedVolumeIndex X := by
  unfold O2CorrectedVolumeIndex
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (ArithmeticQPilotLogVolume.localLogMagnitude_pos (nativeQ X))

/-- Actual counterexample: at volume index 1 the corrected identification is
still false. -/
theorem o2Corrected_false_of_index_one
    (h : fPlaceVolumeIndex X = 1) :
    ¬ O2CorrectedVolumeIdentification X := by
  intro hcorr
  have hidx := (o2Corrected_iff_index X).mp hcorr
  have hone : (fPlaceVolumeIndex X : ℝ) = 1 := by exact_mod_cast h
  rw [hone] at hidx
  have hgt := one_lt_O2CorrectedVolumeIndex X
  linarith

end ABCBridge.N8.O2CorrectedVolumeIndex
