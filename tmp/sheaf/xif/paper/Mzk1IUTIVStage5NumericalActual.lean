import tmp.sheaf.xif.paper.Mzk1IUTIVStage5ABCFormActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1IUTIVStage5NumericalActual — Stage-5 consumer on the ABC form

Consumes the Stage-5 ABC-form numerical core: the literal height comparison and
the main log-volume estimate imply the ABC-form additive bound and ABCConjecture.
No closure claim; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual

theorem additiveHeightBound_of_literalLogVolumeEstimates
    (logVolume : Nat → Nat → Nat → ℝ) (hullVolume : ℝ)
    (hheight : ∀ δ : ℝ, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (hmain : ∀ δ : ℝ, 0 < δ → ∃ D : ℝ,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D) :
    ABCFormAdditiveHeightBound :=
  abcFormAdditiveHeightBound_of_literalEstimates logVolume hullVolume hheight hmain

theorem abcConjecture_of_literalLogVolumeEstimates
    (logVolume : Nat → Nat → Nat → ℝ) (hullVolume : ℝ)
    (hheight : ∀ δ : ℝ, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (hmain : ∀ δ : ℝ, 0 < δ → ∃ D : ℝ,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D) :
    ABCConjecture :=
  abcConjecture_of_literalEstimates logVolume hullVolume hheight hmain

end LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual

end
