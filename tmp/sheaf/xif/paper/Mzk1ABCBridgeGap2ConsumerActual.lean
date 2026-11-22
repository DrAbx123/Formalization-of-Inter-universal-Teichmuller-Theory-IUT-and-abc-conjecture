/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.A502HcompToRealAdapterActual

/-! # A572: ABC Stage5 Gap-2 consumer (A502 adapter + minimal named estimate) -/

noncomputable section

namespace LeanFormal.IUT.Objects.ABCBridgeGap2

open LeanFormal.IUT.Objects.HcompAdapter

/-- Minimal named analytic estimate of Gap 2 (`regionVolume_le_normalizedWeight`):
the normalized region volume is bounded by `(1+eps)*weight + theta + D` in ENNReal
form.  This is the only named content here; the ENNReal/Real conversion below is proved. -/
def SNamed (regionVolume : ENNReal) (eps weight theta D : ℝ) : Prop :=
  regionVolume ≤ ENNReal.ofReal ((1 + eps) * weight + theta + D)

/-- Gap-2 consumer: the named ENNReal-form estimate yields the paper's real-form
`regionVolume.toReal ≤ (1+eps)*weight + theta + D` (by the A502 adapter). -/
theorem gap2_real_bound {regionVolume : ENNReal} {eps weight theta D : ℝ}
    (hR : 0 ≤ (1 + eps) * weight + theta + D)
    (hS : SNamed regionVolume eps weight theta D) :
    regionVolume.toReal ≤ (1 + eps) * weight + theta + D :=
  normalized_volume_toReal_bound hR hS

/-- Conversely, the real form with finiteness gives the named ENNReal estimate. -/
theorem gap2_ennreal_bound {regionVolume : ENNReal} {eps weight theta D : ℝ}
    (hfin : regionVolume ≠ ⊤) (hR : 0 ≤ (1 + eps) * weight + theta + D)
    (h : regionVolume.toReal ≤ (1 + eps) * weight + theta + D) :
    SNamed regionVolume eps weight theta D :=
  normalized_volume_ennreal_bound hfin hR h

end LeanFormal.IUT.Objects.ABCBridgeGap2
