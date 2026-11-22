import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import tmp.sheaf.xif.paper.ABCGap2FiniteC3SupplyActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8Cor312ToABCBridgeActual
open LeanFormal.IUT

universe u

/-- Attempted actual P5/P6 weight bound used by
`cor312GapAssembly_epsilonComparisonOfReducedInputs`: the arithmetic weight of
an ABC point is bounded by the normalized comparison-region volume. -/
theorem p8Cor312WeightBoundActual
    {X : Type u} (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) {eps : ℝ} (heps : 0 ≤ eps) :
    ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal := by
  intro a b c habc
  exact ?_

end LeanFormal.IUT.XiFPaper.Mzk1P8Cor312ToABCBridgeActual
end
