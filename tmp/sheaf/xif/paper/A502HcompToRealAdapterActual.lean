/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # A502 hcomp adapter: ENNReal/Real conversion lemmas for normalized volume bounds -/

namespace LeanFormal.IUT.Objects.HcompAdapter

theorem toReal_le_toReal_of_le {a b : ENNReal} (h : a ≤ b) (hb : b ≠ ⊤) :
    a.toReal ≤ b.toReal := ENNReal.toReal_mono hb h

theorem toReal_le_of_le_ofReal {a : ENNReal} {r : ℝ} (hr : 0 ≤ r)
    (h : a ≤ ENNReal.ofReal r) : a.toReal ≤ r := by
  have h2 : a.toReal ≤ (ENNReal.ofReal r).toReal := 
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal hr] at h2

theorem le_ofReal_of_toReal_le {a : ENNReal} {r : ℝ} (ha : a ≠ ⊤) (hr : 0 ≤ r)
    (h : a.toReal ≤ r) : a ≤ ENNReal.ofReal r := by
  rw [ENNReal.le_ofReal_iff_toReal_le ha hr]
  exact h

theorem normalized_volume_toReal_bound {a : ENNReal} {eps w theta D : ℝ}
    (hr : 0 ≤ (1 + eps) * w + theta + D)
    (h : a ≤ ENNReal.ofReal ((1 + eps) * w + theta + D)) :
    a.toReal ≤ (1 + eps) * w + theta + D := 
  toReal_le_of_le_ofReal hr h

theorem normalized_volume_ennreal_bound {a : ENNReal} {eps w theta D : ℝ}
    (ha : a ≠ ⊤) (hr : 0 ≤ (1 + eps) * w + theta + D)
    (h : a.toReal ≤ (1 + eps) * w + theta + D) :
    a ≤ ENNReal.ofReal ((1 + eps) * w + theta + D) := 
  le_ofReal_of_toReal_le ha hr h

theorem normalized_volume_toReal_bound_mono {a : ENNReal} {eps w theta D D' : ℝ}
    (hr : 0 ≤ (1 + eps) * w + theta + D)
    (h : a ≤ ENNReal.ofReal ((1 + eps) * w + theta + D)) (hD : D ≤ D') :
    a.toReal ≤ (1 + eps) * w + theta + D' := by
  have h1 := normalized_volume_toReal_bound hr h
  linarith

end LeanFormal.IUT.Objects.HcompAdapter
