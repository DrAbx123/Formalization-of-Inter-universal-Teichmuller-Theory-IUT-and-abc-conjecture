import tmp.sheaf.xif.paper.Mzk1IUTIVStage5ABCFormActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi ABC height/region consumer

Consumes the green ABC-form additive height bound contract from the Stage-5 file
(`abcConjecture_of_abcFormAdditiveHeightBound`).  The height/region comparison is
the explicit named `ABCFormAdditiveHeightBound` input; no axiom/True. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIABCFormHeightConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual

structure StepXIABCHeightRegionInput where
  heightRegionBound : ABCFormAdditiveHeightBound

theorem stepxi_abcForm_heightRegion (I : StepXIABCHeightRegionInput) :
    ABCConjecture :=
  abcConjecture_of_abcFormAdditiveHeightBound I.heightRegionBound

theorem stepxi_abcForm_literalEstimates
    (logVolume : Nat → Nat → Nat → Real) (hullVolume : Real)
    (hheight : ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (hmain : ∀ δ : Real, 0 < δ → ∃ D : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D) :
    ABCConjecture :=
  abcConjecture_of_literalEstimates logVolume hullVolume hheight hmain

end LeanFormal.IUT.XiFPaper.Mzk1StepXIABCFormHeightConsumerActual

end
