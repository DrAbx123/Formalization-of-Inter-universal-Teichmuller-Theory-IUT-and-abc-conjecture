/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1LanaBridgeAuditActual
import tmp.sheaf.xif.paper.Mzk1GapStructuralConsequencesActual
import tmp.sheaf.xif.paper.Mzk1IUTIVStage5ABCFormActual

/-! # A652 hull: REAL mathematical content for Gap1/Gap2

Substantive theorems about the two exact gap shapes (no interface shims):

1. **Gap 2 is automatic for hull-contained regions** (with `D = 0`): if every
   comparison region of an ABC triple lies in the finite hull, then
   `regionVol ≤ (1+ε)·weight + hullVol` because `regionVol ≤ hullVol` and the
   weight term is nonnegative.  So for such regions the *only* genuine obstruction
   is Gap 1 — matching A618/A631 structural results.
2. **Gap 2 does not imply Gap 1**: the hull region itself has Gap 2 (trivially)
   but Gap 1 is impossible for it (bounded region volume vs unbounded ABC heights).
3. **Gap 1 + Gap 2 ⇒ ABCConjecture**: instantiating the green Stage-5 rung
   `abcConjecture_of_literalEstimates` with the abstract region volumes gives the
   paper's conditional reduction from the two estimates to ABC.  The two gap
   Props are still hypotheses; nothing is claimed proved.

No object is changed; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GapRealContentActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1GapStructuralConsequencesActual
open Mzk1LanaBridgeAuditActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {X : Type*}

/-! ## 1. Gap 2 is automatic for bounded (e.g. hull-contained) regions -/

/-- If the region log-volume exceeds the hull log-volume by at most a fixed `B` on
all ABC triples, then Gap 2 holds with `D = B` (the weight term is nonnegative). -/
theorem gap2_of_volume_le_hull_add (W : LeanFormal.IUT.IQHullLogVolumeInterface X)
    (region : Nat → Nat → Nat → Set X) (B : Real)
    (h : ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (region a b c)).toReal ≤
        (W.logVolume W.hull).toReal + B) :
    Gap2Prop W region := by
  intro ε hε
  refine ⟨B, ?_⟩
  intro a b c habc
  have hV := h a b c habc
  have hw : 0 ≤ (1 + ε) * arithmeticWeight (abcRationalPoint a c) :=
    mul_nonneg (by linarith) (arithmeticWeight_nonneg_local _)
  linarith

/-- **Gap 2 is automatic for regions contained in the finite hull** (`D = 0`). -/
theorem gap2_of_subset_hull (W : LeanFormal.IUT.IQHullLogVolumeInterface X)
    (hfin : W.logVolume W.hull < ⊤)
    (region : Nat → Nat → Nat → Set X)
    (hsub : ∀ a b c : Nat, IsABCTriple a b c → region a b c ⊆ W.hull) :
    Gap2Prop W region := by
  refine gap2_of_volume_le_hull_add W region 0 ?_
  intro a b c habc
  have hle : W.logVolume (region a b c) ≤ W.logVolume W.hull :=
    W.logVolume_mono (hsub a b c habc)
  have hto : (W.logVolume (region a b c)).toReal ≤ (W.logVolume W.hull).toReal :=
    ENNReal.toReal_mono (ne_of_lt hfin) hle
  linarith

/-- The hull region itself satisfies Gap 2 trivially (no finiteness needed). -/
theorem gap2_hull_region (W : LeanFormal.IUT.IQHullLogVolumeInterface X) :
    Gap2Prop W (fun _ _ _ => W.hull) := by
  intro ε hε
  refine ⟨0, ?_⟩
  intro a b c _
  have hw : 0 ≤ (1 + ε) * arithmeticWeight (abcRationalPoint a c) :=
    mul_nonneg (by linarith) (arithmeticWeight_nonneg_local _)
  linarith

/-! ## 2. Gap 2 does not imply Gap 1 (separation) -/

/-- **Separation**: for a finite hull, the hull region has Gap 2 but not Gap 1;
hence Gap 2 alone is strictly weaker than Gap 1. -/
theorem gap2_not_implying_gap1 (W : LeanFormal.IUT.IQHullLogVolumeInterface X)
    (hfin : W.logVolume W.hull < ⊤) :
    Gap2Prop W (fun _ _ _ => W.hull) ∧
      ¬ Gap1Prop W (fun _ _ _ => W.hull) :=
  ⟨gap2_hull_region W,
    gap1_impossible_of_region_in_finite_hull W hfin _
      (fun _ _ _ _ => Set.Subset.refl _)⟩

/-! ## 3. Gap 1 + Gap 2 imply ABC (the paper reduction) -/

/-- **Gap 1 + Gap 2 ⇒ ABCConjecture**: instantiate the green Stage-5 rung with the
abstract comparison-region volumes.  This is the conditional paper reduction; the
two gap Props remain explicit hypotheses. -/
theorem abc_of_gapShapes (W : LeanFormal.IUT.IQHullLogVolumeInterface X)
    (region : Nat → Nat → Nat → Set X)
    (h1 : Gap1Prop W region) (h2 : Gap2Prop W region) :
    ABCConjecture :=
  abcConjecture_of_literalEstimates
    (fun a b c => (W.logVolume (region a b c)).toReal)
    ((W.logVolume W.hull).toReal) h1 h2

def gapRealContentRows : List (String × String × String) :=
  [ ("Gap2 automatic for hull-contained regions", "gap2_of_subset_hull", "PROVED (D = 0)"),
    ("Gap2 strictly weaker than Gap1", "gap2_not_implying_gap1", "PROVED (separation)"),
    ("Gap1+Gap2 => ABC", "abc_of_gapShapes", "PROVED (conditional on the two gaps)"),
    ("scope", "real math; gaps NOT proved; ABC gate NOT passed", "INTEGRITY") ]

theorem gapRealContentRows_length : gapRealContentRows.length = 4 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapRealContentActual.gap2_of_subset_hull
#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapRealContentActual.gap2_not_implying_gap1
#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapRealContentActual.abc_of_gapShapes

end LeanFormal.IUT.XiFPaper.Mzk1GapRealContentActual

end