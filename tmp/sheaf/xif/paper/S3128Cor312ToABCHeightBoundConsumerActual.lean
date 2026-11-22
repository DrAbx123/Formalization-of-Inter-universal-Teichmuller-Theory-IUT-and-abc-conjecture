import tmp.sheaf.xif.paper.S3128Cor312ToABCInputConsumerActual
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3128Cor312ToABCInputConsumerActual

namespace LeanFormal.IUT.XiFPaper.S3128Cor312ToABCHeightBoundConsumerActual
universe u

/-- The ABC-style arithmetic-weight height bound used as the right-hand side of
`abcConjecture_iff_abcArithmeticWeightHeightBound`. -/
def S3128ABCHeightBound : Prop :=
  ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A

/-- The arithmetic-weight height bound is equivalent to `ABCConjecture`. -/
theorem S3128ABCHeightBound_iff_abcConjecture :
    S3128ABCHeightBound ↔ ABCConjecture :=
  abcConjecture_iff_abcArithmeticWeightHeightBound.symm

/-- The Cor312 input yields the height-bound statement. -/
theorem S3128ABCHeightBound_of_cor312Input
    (D : S3128Cor312ToABCInput.{u}) : S3128ABCHeightBound :=
  S3128Cor312ToABCInput_heightBound D

/-- Cross-check: input -> height bound -> ABCConjecture, matching the direct route. -/
theorem S3128ABCConjecture_of_cor312Input_via_heightBound
    (D : S3128Cor312ToABCInput.{u}) : ABCConjecture :=
  S3128ABCHeightBound_iff_abcConjecture.mp (S3128ABCHeightBound_of_cor312Input D)

/-- Converse calibration: ABC yields the height-bound form. -/
theorem S3128ABCHeightBound_of_abcConjecture
    (h : ABCConjecture) : S3128ABCHeightBound :=
  S3128ABCHeightBound_iff_abcConjecture.mpr h

#check S3128ABCHeightBound
#check S3128ABCHeightBound_iff_abcConjecture
#check S3128ABCHeightBound_of_cor312Input
#check S3128ABCConjecture_of_cor312Input_via_heightBound
#check S3128ABCHeightBound_of_abcConjecture

end LeanFormal.IUT.XiFPaper.S3128Cor312ToABCHeightBoundConsumerActual
end