import tmp.sheaf.xif.paper.S3128Cor312ToABCHeightBoundConsumerActual
import LeanFormal.IUT.ABCBridge.Statement
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3128Cor312ToABCInputConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Cor312ToABCHeightBoundConsumerActual

namespace LeanFormal.IUT.XiFPaper.S3128ABCRpowConsumerActual
universe u

/-- The radical-power `ABCInequality` form of ABC, packaged as a Prop. -/
def S3128ABCRpowBound : Prop :=
  ∀ epsilon : Real, 0 < epsilon → ∃ K : Real, 0 < K ∧
    ∀ a b c : Nat, IsABCTriple a b c → ABCInequality epsilon K a b c

/-- The rpow form is definitionally the standard `ABCConjecture`. -/
theorem S3128ABCRpowBound_iff_abcConjecture :
    S3128ABCRpowBound ↔ ABCConjecture :=
  Iff.rfl

/-- Height-bound form implies the rpow form. -/
theorem S3128ABCRpowBound_of_heightBound
    (h : S3128ABCHeightBound) : S3128ABCRpowBound :=
  S3128ABCRpowBound_iff_abcConjecture.mpr
    (S3128ABCHeightBound_iff_abcConjecture.mp h)

/-- rpow form implies the height-bound form. -/
theorem S3128ABCHeightBound_of_rpowBound
    (h : S3128ABCRpowBound) : S3128ABCHeightBound :=
  S3128ABCHeightBound_iff_abcConjecture.mpr
    (S3128ABCRpowBound_iff_abcConjecture.mp h)

/-- Full consumer chain: Cor312 input -> height bound -> rpow ABCInequality form. -/
theorem S3128ABCRpowBound_of_cor312Input
    (D : S3128Cor312ToABCInput.{u}) : S3128ABCRpowBound :=
  S3128ABCRpowBound_of_heightBound (S3128ABCHeightBound_of_cor312Input D)

#check S3128ABCRpowBound
#check S3128ABCRpowBound_iff_abcConjecture
#check S3128ABCRpowBound_of_heightBound
#check S3128ABCHeightBound_of_rpowBound
#check S3128ABCRpowBound_of_cor312Input

end LeanFormal.IUT.XiFPaper.S3128ABCRpowConsumerActual
end