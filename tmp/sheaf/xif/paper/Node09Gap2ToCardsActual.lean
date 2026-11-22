import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import tmp.sheaf.xif.paper.Node09RegionMonoActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Node09RegionMonoActual

namespace LeanFormal.IUT.XiFPaper.Node09Gap2ToCardsActual

universe u

/-- If the gap-2 region-volume field of a comparison is supplied, then the
singleton point-volume bound follows by monotonicity, with the hull term absorbed
into the additive constant. -/
theorem hpoint_of_comparison
    {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon) :
    ∃ D1 : Real, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume {W.scaleShift (C.logShellPoint a b c)}).toReal ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + D1 := by
  obtain ⟨D, hD⟩ := C.regionVolume_le_normalizedWeight
  refine ⟨(W.logVolume W.hull).toReal + D, fun a b c habc => ?_⟩
  have hmono : W.logVolume {W.scaleShift (C.logShellPoint a b c)} ≤
      W.logVolume (normalizedComparisonRegion W C.logShellPoint a b c) :=
    singletonVolume_le_regionVolume X W C.logShellPoint a b c
  have hfin := C.comparisonRegion_logVolume_lt_top a b c habc
  have hle : (W.logVolume {W.scaleShift (C.logShellPoint a b c)}).toReal ≤
      (W.logVolume (normalizedComparisonRegion W C.logShellPoint a b c)).toReal :=
    ENNReal.toReal_mono (ne_of_lt hfin) hmono
  have hD' := hD a b c habc
  calc (W.logVolume {W.scaleShift (C.logShellPoint a b c)}).toReal
      ≤ (W.logVolume (normalizedComparisonRegion W C.logShellPoint a b c)).toReal := hle
    _ ≤ (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D := hD'
    _ = (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          ((W.logVolume W.hull).toReal + D) := by ring

/-- Exact search result: the region-volume bound is exactly the frozen gap-2
field; no unconditional donor exists in the tree. -/
def Node09Gap2ToCardsResidual : List String :=
  [ "hpoint (singleton point-volume bound) is derived from the gap-2 region-volume field Cor312EpsilonArithmeticComparison.regionVolume_le_normalizedWeight by monotonicity singleton <= region and absorbing the hull term into D1",
    "the remaining input is exactly the frozen gap-2 paper link regionVolume_le_normalizedWeight (IUT IV main log-volume estimate); Mzk1LocalEstimateConsumerQpilotActual and Mzk1GapCorrespondenceAuditQpilotActual identify it as the IUT IV local-estimate comparison, and Mzk1ABCEntryGap2QpilotActual only consumes it",
    "no donor produces regionVolume_le_normalizedWeight; it stays a paper-level input, no inhabitant/fake" ]

end LeanFormal.IUT.XiFPaper.Node09Gap2ToCardsActual
