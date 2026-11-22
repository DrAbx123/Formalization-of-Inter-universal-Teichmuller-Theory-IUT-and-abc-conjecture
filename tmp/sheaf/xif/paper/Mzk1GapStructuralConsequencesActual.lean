/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1LanaBridgeAuditActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
# A631 Gap 1 STRUCTURAL consequences (mainline)

Substantive consequences of Gap 1 (`height_le_normalizedRegionVolume`), proved from
the green unbounded-height theorem `abcRationalPoint_logHeight_unbounded`:

* any region satisfying the height comparison must have **unbounded log-volume**;
* consequently Gap 1 cannot hold for a region contained in the finite hull — the
  comparison region must genuinely leave the hull (matching the paper shape and the
  no-height-dictionary obstruction `no_heightDictionary_into_finiteHull`).

These are structural theorems about Gap 1, not a proof of Gap 1.  No object is
changed; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1GapStructuralConsequencesActual

open LeanFormal.IUT
open Mzk1LanaBridgeAuditActual

variable {X : Type*}

/-- **Gap 1 forces unbounded region log-volume**: the height comparison
  `logHeight ≤ (1+ε)·regionVol` on all ABC triples implies that the comparison region
  has arbitrarily large log-volume (otherwise unbounded heights would be bounded). -/
theorem gap1_forces_unbounded_regionVolume (W : IQHullLogVolumeInterface X)
    (region : Nat → Nat → Nat → Set X) (h : Gap1Prop W region) :
    ∀ B : ℝ, ∃ a b c : Nat, IsABCTriple a b c ∧
      B < (W.logVolume (region a b c)).toReal := by
  intro B
  obtain ⟨a, b, c, habc, hgt⟩ := abcRationalPoint_logHeight_unbounded (2 * B)
  have h1 := h 1 zero_lt_one a b c habc
  have h2 : Height.logHeight₁ (abcRationalPoint a c) ≤
      2 * (W.logVolume (region a b c)).toReal := by
    nlinarith [h1]
  have hnonneg : 0 ≤ (W.logVolume (region a b c)).toReal := ENNReal.toReal_nonneg
  exact ⟨a, b, c, habc, by nlinarith⟩

/-- **Gap 1 is impossible inside a finite hull**: if the comparison region of every
  ABC triple lies in the (finite-log-volume) hull, no height comparison of Gap 1 shape
  can hold.  This is the structural counterpart of
  `no_heightDictionary_into_finiteHull`. -/
theorem gap1_impossible_of_region_in_finite_hull (W : IQHullLogVolumeInterface X)
    (hfin : W.logVolume W.hull < ⊤) (region : Nat → Nat → Nat → Set X)
    (hsub : ∀ a b c : Nat, IsABCTriple a b c → region a b c ⊆ W.hull) :
    ¬ Gap1Prop W region := by
  intro h
  have hbnd : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        2 * (W.logVolume W.hull).toReal := by
    intro a b c habc
    have h1 := h 1 zero_lt_one a b c habc
    have h2 : (W.logVolume (region a b c)).toReal ≤
        (W.logVolume W.hull).toReal :=
      ENNReal.toReal_mono (ne_of_lt hfin) (W.logVolume_mono (hsub a b c habc))
    calc Height.logHeight₁ (abcRationalPoint a c) ≤
          2 * (W.logVolume (region a b c)).toReal := by nlinarith [h1]
        _ ≤ 2 * (W.logVolume W.hull).toReal :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
  obtain ⟨a, b, c, habc, hgt⟩ := abcRationalPoint_logHeight_unbounded
    (2 * (W.logVolume W.hull).toReal)
  exact not_lt_of_ge (hbnd a b c habc) hgt

end LeanFormal.IUT.XiFPaper.Mzk1GapStructuralConsequencesActual

end
/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapStructuralConsequencesActual.gap1_forces_unbounded_regionVolume
#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapStructuralConsequencesActual.gap1_impossible_of_region_in_finite_hull