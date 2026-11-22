import tmp.sheaf.n8.closure.EtaAnabAtFPlace
import tmp.sheaf.n8.closure.EtaFPlaceComparisonProof
import tmp.sheaf.n8.closure.EtaFPlaceSignedComparison
import tmp.sheaf.n8.closure.EtaValueGroupLineActual
import tmp.sheaf.n8.closure.C9QPilotRegion
import Mathlib

/-!
# O2 constructed identification

The O2 proposition is

  etaPilot = ofAdd (etaRssAtFPlace.logVolume).

This file tests it against actual carriers.  The F-place etaAnab log-volume is
nonnegative (it is Real.log of a positive volume index), while the native q
pilot has negative additive log qPilotSignedLog.  Hence the naive equality is
FALSE, not merely unproved: its two sides have opposite signs.

The exact corrected source identification is conditional on the signed F-place
comparison: when the positive F-shell log-volume equals the q log-magnitude,
ofAdd logVolume is the inverse of etaPilot.  The missing source construction is
precisely the signed comparison (already shown false at volume index 1).
-/

noncomputable section

namespace ABCBridge.N8.O2ConstructedIdentification

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open LeanFormal.IUT.N8Closure.EtaFPlaceComparisonProof
open LeanFormal.IUT.N8Closure.EtaFPlaceSignedComparison
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The F-place etaAnab log-volume is the production F-shell log-volume. -/
theorem etaRssAtFPlace_logVolume_eq :
    (etaRssAtFPlace (X := X)).logVolume = fPlaceLogVolume X :=
  rfl

/-- The F-place etaAnab log-volume is nonnegative. -/
theorem etaRssAtFPlace_logVolume_nonneg :
    0 ≤ (etaRssAtFPlace (X := X)).logVolume := by
  rw [etaRssAtFPlace_logVolume_eq]
  exact fPlaceLogVolume_nonneg X

/-- The additive log of the native q pilot is the actual negative q log. -/
theorem etaPilot_toAdd :
    Multiplicative.toAdd (etaPilot X) = qPilotSignedLog X := by
  simp [etaPilot, qPilotKummerRelativeVolume_eq]

/-- Actual sign obstruction: etaPilot is below the identity element
(additive log < 0). -/
theorem etaPilot_additiveLog_neg :
    Multiplicative.toAdd (etaPilot X) < 0 := by
  rw [etaPilot_toAdd]
  exact qPilotSignedLog_neg X

/-- The naive O2 identification is false: the q pilot has negative additive
log, while the F-place log-volume is nonnegative. -/
theorem no_naive_identification :
    ¬ (etaPilot X = Multiplicative.ofAdd (etaRssAtFPlace (X := X)).logVolume) := by
  intro h
  have hlog : Multiplicative.toAdd (etaPilot X) =
      (etaRssAtFPlace (X := X)).logVolume := by
    simpa using congrArg Multiplicative.toAdd h
  rw [etaPilot_toAdd] at hlog
  have hq : qPilotSignedLog X < 0 := qPilotSignedLog_neg X
  have hV : 0 ≤ (etaRssAtFPlace (X := X)).logVolume :=
    etaRssAtFPlace_logVolume_nonneg X
  linarith

/-- Corrected source identification: under the actual signed F-place
comparison, the F-place log-volume class is the inverse of the q pilot.  This
is not the naive target; it is the sign-correct source comparison. -/
theorem corrected_identification_of_signedComparison
    (h : EtaFPlaceSignedComparisonTarget X) :
    Multiplicative.ofAdd (etaRssAtFPlace (X := X)).logVolume = (etaPilot X)⁻¹ := by
  have hlog : (etaRssAtFPlace (X := X)).logVolume = qPilotLogMagnitude X := by
    rw [etaRssAtFPlace_logVolume_eq]
    rw [EtaFPlaceSignedComparisonTarget] at h
    rw [h, neg_fPlaceNormalizedQVolume_eq_magnitude]
  have hp : etaPilot X = Multiplicative.ofAdd (qPilotSignedLog X) := by
    simp [etaPilot, qPilotKummerRelativeVolume_eq]
  have hmag : qPilotLogMagnitude X = -qPilotSignedLog X := rfl
  rw [hlog, hp, hmag]
  simp

/-- Exact missing source construction: the signed F-place comparison.  The
decisive sign obstruction above shows the naive O2 identification cannot be
repaired without the sign; the signed comparison is the precise gap. -/
def O2MissingSignedComparison : Prop :=
  EtaFPlaceSignedComparisonTarget X

end ABCBridge.N8.O2ConstructedIdentification
