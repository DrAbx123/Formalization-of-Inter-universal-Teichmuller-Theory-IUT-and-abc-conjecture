/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import tmp.sheaf.xif.paper.Mzk1LanaBridgeAuditActual

/-!
# A652 Gap1/Gap2 REAL mathematical content (mainline)

Genuine interface-level consequences (no shortcuts, no theorem conclusions changed):

* `scaleShift_unitRegion_toReal_le`: the scaled unit region has at most the unit
  region's real log-volume (paper Remark 3.9.5 normalization);
* `hull_toReal_le_unitRegion`: hence the θ-pilot hull's real log-volume is at most the
  unit region's (Cor 3.12 finiteness + normalization);
* `height_comparison_mono`: the Gap1 height bound is monotone in `ε` (for nonnegative
  region log-volume);
* `gap2_unitRegion_version`: Gap2 with the θ-hull bound replaced by the (weaker, but
  canonical) unit-region bound.

These are real implications, not a proof of either gap; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1GapMathematicalContentActual

open LeanFormal.IUT
open Mzk1LanaBridgeAuditActual

variable {X : Type*} (W : IQHullLogVolumeInterface X)

/-- The scaled unit region has at most the unit region's real log-volume. -/
theorem scaleShift_unitRegion_toReal_le :
    (W.logVolume (W.scaleShift '' W.unitRegion)).toReal ≤
      (W.logVolume W.unitRegion).toReal :=
  ENNReal.toReal_mono (ne_of_lt W.unitRegion_logVolume_lt_top)
    W.scaleShift_unitRegion_logVolume_le

/-- The θ-pilot hull's real log-volume is at most the unit region's. -/
theorem hull_toReal_le_unitRegion :
    (W.logVolume W.hull).toReal ≤ (W.logVolume W.unitRegion).toReal :=
  ENNReal.toReal_mono (ne_of_lt W.unitRegion_logVolume_lt_top)
    (le_trans (W.logVolume_mono W.hull_subset_scaleShift)
      W.scaleShift_unitRegion_logVolume_le)

/-- The Gap1 height comparison is monotone in the parameter `ε`. -/
theorem height_comparison_mono {ε₁ ε₂ : ℝ} (hle : ε₁ ≤ ε₂)
    (region : Nat → Nat → Nat → Set X)
    (h : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε₁) * (W.logVolume (region a b c)).toReal) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε₂) * (W.logVolume (region a b c)).toReal := by
  intro a b c habc
  have h1 := h a b c habc
  have hnonneg : 0 ≤ (W.logVolume (region a b c)).toReal := ENNReal.toReal_nonneg
  have hcoef : 1 + ε₁ ≤ 1 + ε₂ := by linarith
  nlinarith

/-- Gap2 with the θ-hull term replaced by the canonical unit-region bound. -/
theorem gap2_unitRegion_version (region : Nat → Nat → Nat → Set X)
    (h : Mzk1LanaBridgeAuditActual.Gap2Prop W region) :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (region a b c)).toReal ≤
        (1 + ε) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.unitRegion).toReal + D := by
  intro ε hε
  obtain ⟨D, hD⟩ := h ε hε
  refine ⟨D, fun a b c habc => ?_⟩
  have h1 := hD a b c habc
  have h2 := hull_toReal_le_unitRegion W
  nlinarith

end LeanFormal.IUT.XiFPaper.Mzk1GapMathematicalContentActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapMathematicalContentActual.hull_toReal_le_unitRegion
#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapMathematicalContentActual.height_comparison_mono
#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapMathematicalContentActual.gap2_unitRegion_version