import tmp.sheaf.xif.paper.Mzk1StepXIHeightEstimateInterfaceActual
import tmp.sheaf.xif.paper.Mzk1StepXIVolumeEstimateInterfaceActual
import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoGapsFormalActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi gap correspondence: two estimates <-> two-gap input

Concrete correspondence between the HeightEstimate/VolumeEstimate consumer
interfaces and `StepXIABCTwoGaps`. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGapCorrespondenceActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIHeightEstimateInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIVolumeEstimateInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoGapsFormalActual

theorem stepxi_gap_correspondence
    (logVolume : Nat → Nat → Nat → Real) (hullVolume : Real)
    (height_le : ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (main_le : ∀ δ : Real, 0 < δ → ∃ D : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D) :
    StepXIABCTwoGaps where
  logVolume := logVolume
  hullVolume := hullVolume
  height_gap := height_le
  main_gap := main_le

theorem stepxi_gap_correspondence_ABC
    (logVolume : Nat → Nat → Nat → Real) (hullVolume : Real)
    (height_le : ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (main_le : ∀ δ : Real, 0 < δ → ∃ D : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D) :
    ABCConjecture :=
  stepxi_twoGaps_ABC (stepxi_gap_correspondence logVolume hullVolume height_le main_le)

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGapCorrespondenceActual

end
