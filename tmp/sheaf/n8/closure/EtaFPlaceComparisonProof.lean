import tmp.sheaf.n8.closure.EtaFPlaceNormalizedComparison

/-!
# Eta F-place comparison proof attempt

The F-place normalized q volume is the production selectedLowerSignedLog over
the singleton {nativeFPlaceOverBad X}; it reduces to the actual signed q log,
which is strictly negative.  The F-place shell logVolume is a nonnegative
logarithm of the positive production volume index.  Therefore
EtaFPlaceNormalizedComparisonTarget is FALSE for every native X.

No arbitrary normalization or raw equality is used: this is a sign obstruction
from production values.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaFPlaceComparisonProof

open scoped Padic

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open LeanFormal.IUT.ArithmeticQPilotGlobalNormalization
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace

variable {l : PrimeGeFive}
variable {X : N8NativeInput l}

/-- The singleton processed q volume is the actual signed log of the native q. -/
theorem fPlaceNormalizedQVolume_eq_signedLog (X : N8NativeInput l) :
    fPlaceNormalizedQVolume X = qPilotSignedLog X := by
  simp [fPlaceNormalizedQVolume, qPilotProcessionNormalizedVolume,
    qPilotSignedLog, qPilotSelectedPlaces, qPilotSelectedParameters,
    selectedLowerSignedLog, Finset.sum_singleton]

/-- The F-place shell logVolume is nonnegative: it is the log of a positive
natural volume index. -/
theorem fPlaceLogVolume_nonneg (X : N8NativeInput l) :
    0 ≤ fPlaceLogVolume X := by
  rw [fPlaceLogVolume]
  have hpos : 0 < fPlaceVolumeIndex X := (fPlaceVolumeConsumer X).index_pos
  have hone : (1 : Nat) ≤ fPlaceVolumeIndex X := Nat.one_le_iff_ne_zero.mpr hpos.ne'
  have honeR : (1 : Real) ≤ (fPlaceVolumeIndex X : Real) := by exact_mod_cast hone
  exact Real.log_nonneg honeR

/-- The production normalized q volume is strictly negative. -/
theorem fPlaceNormalizedQVolume_negative (X : N8NativeInput l) :
    fPlaceNormalizedQVolume X < 0 := by
  rw [fPlaceNormalizedQVolume_eq_signedLog]
  exact qPilotSignedLog_neg X

/-- DECISIVE NO-GO: the F-place normalized comparison equality is false. -/
theorem etaFPlaceNormalizedComparisonTarget_false (X : N8NativeInput l) :
    ¬ EtaFPlaceNormalizedComparisonTarget X := by
  intro h
  have hnonneg := fPlaceLogVolume_nonneg X
  have hneg := fPlaceNormalizedQVolume_negative X
  rw [h] at hnonneg
  linarith

end LeanFormal.IUT.N8Closure.EtaFPlaceComparisonProof
