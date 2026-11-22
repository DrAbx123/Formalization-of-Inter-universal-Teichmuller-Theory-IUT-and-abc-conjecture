import tmp.sheaf.xif.paper.S2765PointMapActual
import tmp.sheaf.xif.paper.S2760MixedSpacePaperFactorActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
open scoped ENNReal nonZeroDivisors Classical
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2766EpsilonComparisonGapActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2765PointMapActual
open LeanFormal.IUT.XiFPaper.S2760MixedSpacePaperFactorActual

universe u

variable (K : Type u) [Field K] [NumberField K]
variable (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ)

/-- The candidate bridge `logShellPoint`, using the actual mixed-space point map. -/
noncomputable def S2766LogShellPoint (a n c : Nat) :
    NumberField.mixedEmbedding.mixedSpace K :=
  abcPointToMixedSpace K (abcRationalPoint a c)

/-- The candidate comparison region on the S2760 mixed-space IQ-hull interface. -/
noncomputable def S2766ComparisonRegion (eps : Real) (a n c : Nat) :
    Set (NumberField.mixedEmbedding.mixedSpace K) :=
  normalizedComparisonRegion (S2760IQHullInterface K J)
    (S2766LogShellPoint K) a n c

/-- Exact epsilon-comparison gap: the two paper comparison inequalities for the
candidate mixed-space logShellPoint. -/
structure S2766EpsilonComparisonGap (eps : Real) where
  height_le_region :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) *
          ((S2760IQHullInterface K J).logVolume
            (S2766ComparisonRegion K J eps a b c)).toReal
  region_le_weight :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      ((S2760IQHullInterface K J).logVolume
        (S2766ComparisonRegion K J eps a b c)).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          ((S2760IQHullInterface K J).logVolume
            (S2760IQHullInterface K J).hull).toReal + D

/-- The exact gap data builds the actual `Cor312EpsilonArithmeticComparison`. -/
noncomputable def S2766EpsilonComparisonOfGap (eps : Real)
    (G : S2766EpsilonComparisonGap K J eps) :
    Cor312EpsilonArithmeticComparison (S2760IQHullInterface K J) eps where
  logShellPoint := S2766LogShellPoint K
  height_le_normalizedRegionVolume := G.height_le_region
  regionVolume_le_normalizedWeight := G.region_le_weight

theorem S2766EpsilonComparisonOfGap_comparisonRegion (eps : Real)
    (G : S2766EpsilonComparisonGap K J eps) (a n c : Nat) :
    (S2766EpsilonComparisonOfGap K J eps G).comparisonRegion a n c =
      S2766ComparisonRegion K J eps a n c := rfl

#check S2766LogShellPoint
#check S2766ComparisonRegion
#check S2766EpsilonComparisonGap
#check S2766EpsilonComparisonOfGap
#print axioms S2766EpsilonComparisonOfGap

end LeanFormal.IUT.XiFPaper.S2766EpsilonComparisonGapActual
end
