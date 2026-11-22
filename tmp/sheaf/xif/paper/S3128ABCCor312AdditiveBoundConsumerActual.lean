import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Audit

namespace LeanFormal.IUT.XiFPaper.S3128ABCCor312AdditiveBoundConsumerActual

universe u

/-- Actual consumer of the ABC height-arithmetic additive contract: at a fixed
`eps > 0`, extract the additive constant `A` from
`ABCHeightWeightAdditiveBoundV2.exists_constant` and feed the proved
`cor312Gap1_height_le_normalizedRegionVolume_of_additiveBound` route.  The
remaining weight/region comparison is explicit (`hweightvol`), not hidden. -/
theorem cor312Gap1_additiveBound_consumer {X : Type u}
    (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (h : ABCHeightWeightAdditiveBoundV2)
    {eps : Real} (heps : 0 < eps)
    (hweightvol : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal) :
    ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) *
          (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal + A := by
  obtain ⟨A, hA⟩ := h.exists_constant heps
  exact ⟨A, fun a b c habc =>
    cor312Gap1_height_le_normalizedRegionVolume_of_additiveBound
      W logShellPoint heps.le hA hweightvol a b c habc⟩

/-- Audit record for the additive-bound consumer. -/
def abcCor312Gap1AdditiveBoundConsumer : Obligation :=
  { id := "ABCBridge.Cor312.gap1-additive-bound-consumer"
    source := "IUT IV Theorem A additive form; IUT III Cor 3.12 gap 1"
    status := VerificationStatus.conditional
    note := "Extracts A from ABCHeightWeightAdditiveBoundV2.exists_constant at eps>0 and applies the proved additive gap-1 reduction; weight/region comparison remains explicit."
    dependsOn :=
      [ "ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison",
        "ABCBridge.Bridge.Cor312ComparisonGapReduction" ] }

#check cor312Gap1_additiveBound_consumer
#check abcCor312Gap1AdditiveBoundConsumer

end LeanFormal.IUT.XiFPaper.S3128ABCCor312AdditiveBoundConsumerActual
end
