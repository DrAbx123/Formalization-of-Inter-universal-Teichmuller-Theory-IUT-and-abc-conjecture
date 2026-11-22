import tmp.sheaf.xif.paper.S2766EpsilonComparisonGapActual
import tmp.sheaf.xif.paper.S2772BridgeConditionalActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open scoped ENNReal nonZeroDivisors Classical Pointwise
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2766EpsilonComparisonGapActual
open LeanFormal.IUT.XiFPaper.S2772BridgeConditionalActual
open LeanFormal.IUT.XiFPaper.S2760MixedSpacePaperFactorActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2776BridgeHeightReduction

universe u
variable (K : Type u) [Field K] [NumberField K]

/-- Height dictionary: logHeight bounded by C times the comparison-region
volume.  This is the explicit missing dictionary; no proof is asserted. -/
def S2776HeightDictionary
    (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ)
    (eps C : Real) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c)
      ≤ C * ((S2760IQHullInterface K J).logVolume
          (S2766ComparisonRegion K J eps a b c)).toReal

/-- The height dictionary with C = 1 + eps is exactly S2766 height_le_region. -/
theorem S2776HeightDictionary_one_add_eq
    (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) (eps : Real) :
    S2776HeightDictionary K J eps (1 + eps) ↔
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c)
          ≤ (1 + eps) * ((S2760IQHullInterface K J).logVolume
              (S2766ComparisonRegion K J eps a b c)).toReal :=
  Iff.rfl

/-- From the height dictionary (C ≤ 1 + eps) one obtains the S2766 height gap. -/
theorem S2776_height_le_region_of_dictionary
    (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ)
    (eps C : Real) (hC : C ≤ 1 + eps)
    (hdict : S2776HeightDictionary K J eps C) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c)
        ≤ (1 + eps) * ((S2760IQHullInterface K J).logVolume
            (S2766ComparisonRegion K J eps a b c)).toReal := by
  intro a b c habc
  have h := hdict a b c habc
  have hnn : 0 ≤ ((S2760IQHullInterface K J).logVolume
      (S2766ComparisonRegion K J eps a b c)).toReal :=
    ENNReal.toReal_nonneg
  have hmul : C * ((S2760IQHullInterface K J).logVolume
      (S2766ComparisonRegion K J eps a b c)).toReal
      ≤ (1 + eps) * ((S2760IQHullInterface K J).logVolume
        (S2766ComparisonRegion K J eps a b c)).toReal :=
    mul_le_mul_of_nonneg_right hC hnn
  exact le_trans h hmul

end LeanFormal.IUT.XiFPaper.S2776BridgeHeightReduction
end
