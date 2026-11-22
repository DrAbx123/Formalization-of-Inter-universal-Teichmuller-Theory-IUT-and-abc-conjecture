import tmp.sheaf.xif.paper.S2776BridgeHeightReduction
import tmp.sheaf.xif.paper.S2772BridgeConditionalActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open scoped ENNReal nonZeroDivisors Classical Pointwise
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2766EpsilonComparisonGapActual
open LeanFormal.IUT.XiFPaper.S2772BridgeConditionalActual
open LeanFormal.IUT.XiFPaper.S2776BridgeHeightReduction
open LeanFormal.IUT.XiFPaper.S2760MixedSpacePaperFactorActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2779BridgeHeightConsumerActual

universe u
variable (K : Type u) [Field K] [NumberField K]
variable (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ)

/-- Assemble S2766 epsilon gap from the height dictionary and region/weight gap. -/
noncomputable def S2779Gap (eps : Real)
    (hdict : S2776HeightDictionary K J eps (1 + eps))
    (hregion : ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      ((S2760IQHullInterface K J).logVolume
          (S2766ComparisonRegion K J eps a b c)).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          ((S2760IQHullInterface K J).logVolume
            (S2760IQHullInterface K J).hull).toReal + D) :
    S2766EpsilonComparisonGap (K := K) (J := J) eps where
  height_le_region := Iff.mp (S2776HeightDictionary_one_add_eq (K := K) (J := J) eps) hdict
  region_le_weight := hregion

/-- Conditional bridge: explicit height dictionary and region/weight hypotheses. -/
noncomputable def S2779Bridge
    (hdict : ∀ (eps : Real), 0 < eps →
      S2776HeightDictionary K J eps (1 + eps))
    (hregion : ∀ (eps : Real), 0 < eps →
      ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
        ((S2760IQHullInterface K J).logVolume
            (S2766ComparisonRegion K J eps a b c)).toReal ≤
          (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
            ((S2760IQHullInterface K J).logVolume
              (S2760IQHullInterface K J).hull).toReal + D) :
    Cor312ToABCBridgeInterface :=
  S2772Bridge K J (fun eps heps =>
    S2779Gap K J eps (hdict eps heps) (hregion eps heps))

end LeanFormal.IUT.XiFPaper.S2779BridgeHeightConsumerActual
end
