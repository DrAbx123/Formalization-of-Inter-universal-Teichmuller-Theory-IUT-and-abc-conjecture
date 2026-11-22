/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # A524: signed log-volume lemmas (Mathlib-only layer) -/

noncomputable section

namespace LeanFormal.IUT.Objects.SignedLogVolumeLemmas

open scoped ENNReal

/-- Signed log-volume of a region: `Real.log` of the finite measure. -/
def signedLogVolume {X : Type*} (measure : Set X → ENNReal) (S : Set X) : ℝ :=
  Real.log ((measure S).toReal)

/-- If the region has measure at most `1`, its signed log-volume is nonpositive. -/
theorem signedLogVolume_nonpos {X : Type*} (measure : Set X → ENNReal) (S : Set X)
    (hfin : measure S ≠ ⊤) (hle : measure S ≤ 1) :
    signedLogVolume measure S ≤ 0 := by
  unfold signedLogVolume
  apply Real.log_nonpos
  · exact ENNReal.toReal_nonneg
  · have h1 : (measure S).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hle
    simpa using h1

/-- Monotonicity: a measure-monotone region inclusion gives the signed inequality
`signedLogVolume qRegion ≤ signedLogVolume hull` (premises: finiteness, positive q measure). -/
theorem signedLogVolume_mono {X : Type*} (measure : Set X → ENNReal)
    (hmono : ∀ {S T : Set X}, S ⊆ T → measure S ≤ measure T)
    {qRegion hull : Set X} (hsub : qRegion ⊆ hull)
    (hq_ne_top : measure qRegion ≠ ⊤) (hh_ne_top : measure hull ≠ ⊤)
    (hq_pos : 0 < (measure qRegion).toReal) :
    signedLogVolume measure qRegion ≤ signedLogVolume measure hull := by
  unfold signedLogVolume
  exact Real.log_le_log hq_pos (ENNReal.toReal_mono hh_ne_top (hmono hsub))

/-- On a `ofReal r` measure, the signed log-volume is `Real.log r`. -/
theorem signedLogVolume_ofReal {X : Type*} (S : Set X) {r : ℝ} (hr : 0 ≤ r) :
    signedLogVolume (fun _ => ENNReal.ofReal r) S = Real.log r := by
  unfold signedLogVolume
  rw [ENNReal.toReal_ofReal hr]

end LeanFormal.IUT.Objects.SignedLogVolumeLemmas
