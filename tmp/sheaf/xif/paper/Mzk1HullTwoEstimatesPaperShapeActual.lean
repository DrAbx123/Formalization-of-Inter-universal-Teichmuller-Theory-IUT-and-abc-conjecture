/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesGapDecompositionActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual
import tmp.sheaf.xif.paper.Mzk1IUTIVStage5ABCFormActual
import Mathlib.Tactic

/-! # A611 hull: HeightEstimate / VolumeEstimate — paper-shape construction

The two IUT IV Thm 1.10 estimates are tracked as `HeightEstimate` and
`VolumeEstimate` in `Mzk1ABCTwoEstimatesGapDecompositionActual`.  This module
gives the standard *paper-shape* construction of each from non-dilated pointwise
bounds, packages them into a `TwoEstimatesPair` with a shared log-volume
functional, and derives `ABCConjecture` through the green `abc_of_pair`.

* height: from `logHeight₁ <= logVolume` and `0 <= logVolume` (one gets the
  `(1+δ)` slack for every `δ > 0` by monotonicity);
* volume: from an additive bound `logVolume <= arithmeticWeight + hullVolume + D`
  with nonnegative arithmetic weight;
* combined: `ABCTwoEstimates` -> `ABCConjecture` (conditional certificate).

No object is changed; the two estimates remain explicit hypotheses.  No
sorry/axiom, no ABC closure claim. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HullTwoEstimatesPaperShapeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesGapDecompositionActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual

/-! ## 1. Height estimate from the non-dilated height bound -/

/-- A non-dilated height bound `h <= L` with `0 <= L` yields the height-estimate
shape `h <= (1+δ) * L` for every `δ > 0`. -/
theorem height_estimate_of_le {L : Nat → Nat → Nat → Real}
    (hL : ∀ a b c, 0 ≤ L a b c)
    (hbound : ∀ a b c, Height.logHeight₁ (abcRationalPoint a c) ≤ L a b c) :
    ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * L a b c := by
  intro δ hδ a b c _
  have h1 : (1 : Real) ≤ 1 + δ := by linarith
  have h2 : L a b c ≤ (1 + δ) * L a b c := by
    calc L a b c = 1 * L a b c := (one_mul _).symm
      _ ≤ (1 + δ) * L a b c := mul_le_mul_of_nonneg_right h1 (hL a b c)
  exact le_trans (hbound a b c) h2

/-- The height gap record from a non-dilated height bound. -/
def HeightEstimateOfLe (L : Nat → Nat → Nat → Real)
    (hL : ∀ a b c, 0 ≤ L a b c)
    (hbound : ∀ a b c, Height.logHeight₁ (abcRationalPoint a c) ≤ L a b c) :
    HeightEstimate where
  logVolume := L
  hheight := height_estimate_of_le hL hbound

/-! ## 2. Volume estimate from the additive (non-dilated) bound -/

/-- A fixed additive bound `L <= w + H + D` with nonnegative `w` yields the
volume-estimate shape with the *same* `D` for every `δ > 0`. -/
theorem volume_estimate_of_additive {L : Nat → Nat → Nat → Real} {H D : Real}
    (hbound : ∀ a b c, L a b c ≤
      arithmeticWeight (abcRationalPoint a c) + H + D) :
    ∀ δ : Real, 0 < δ → ∃ D' : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        L a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) + H + D' := by
  intro δ hδ
  refine ⟨D, ?_⟩
  intro a b c _
  have hw : 0 ≤ arithmeticWeight (abcRationalPoint a c) :=
    arithmeticWeight_nonneg_local _
  have hwδ : 0 ≤ δ * arithmeticWeight (abcRationalPoint a c) :=
    mul_nonneg hδ.le hw
  have hstep : arithmeticWeight (abcRationalPoint a c) + H + D ≤
      (1 + δ) * arithmeticWeight (abcRationalPoint a c) + H + D := by
    nlinarith
  exact le_trans (hbound a b c) hstep

/-- The volume gap record from an additive bound. -/
def VolumeEstimateOfAdditive (L : Nat → Nat → Nat → Real) (H D : Real)
    (hbound : ∀ a b c, L a b c ≤
      arithmeticWeight (abcRationalPoint a c) + H + D) :
    VolumeEstimate where
  logVolume := L
  hullVolume := H
  hmain := volume_estimate_of_additive hbound

/-! ## 3. The decomposed pair and ABC -/

/-- Build the shared-log-volume pair from non-dilated height and additive volume
bounds on the *same* `L`. -/
def TwoEstimatesPairOfBounds (L : Nat → Nat → Nat → Real) (H D : Real)
    (hL : ∀ a b c, 0 ≤ L a b c)
    (hheight : ∀ a b c, Height.logHeight₁ (abcRationalPoint a c) ≤ L a b c)
    (hvolume : ∀ a b c, L a b c ≤
      arithmeticWeight (abcRationalPoint a c) + H + D) :
    TwoEstimatesPair where
  volume := L
  height := HeightEstimateOfLe L hL hheight
  main := VolumeEstimateOfAdditive L H D hvolume
  height_logVolume := rfl
  main_logVolume := rfl

/-- **Conditional ABC from the two non-dilated estimates on a common log-volume.** -/
theorem abc_of_nondilated_bounds (L : Nat → Nat → Nat → Real) (H D : Real)
    (hL : ∀ a b c, 0 ≤ L a b c)
    (hheight : ∀ a b c, Height.logHeight₁ (abcRationalPoint a c) ≤ L a b c)
    (hvolume : ∀ a b c, L a b c ≤
      arithmeticWeight (abcRationalPoint a c) + H + D) :
    ABCConjecture :=
  abc_of_pair (TwoEstimatesPairOfBounds L H D hL hheight hvolume)

/-- Status table. -/
def twoEstimatesPaperShapeRows : List (String × String × String) :=
  [ ("height estimate from non-dilated bound", "height_estimate_of_le", "PROVED"),
    ("volume estimate from additive bound", "volume_estimate_of_additive", "PROVED"),
    ("shared-log-volume pair", "TwoEstimatesPairOfBounds", "PROVED"),
    ("conditional ABC", "abc_of_nondilated_bounds", "PROVED (conditional on hheight/hvolume)") ]

theorem twoEstimatesPaperShapeRows_length : twoEstimatesPaperShapeRows.length = 4 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1HullTwoEstimatesPaperShapeActual.abc_of_nondilated_bounds

end LeanFormal.IUT.XiFPaper.Mzk1HullTwoEstimatesPaperShapeActual

end