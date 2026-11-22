import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-!
# ShehddHullFrozenSpecConsumerActualAdapted — consumer API for the frozen hull/det log-volume spec

STEP 0 prior-art (reuse only): HolomorphicHull/HullDeterminantLogVolumeReduction.lean defines
`HullDeterminantLogVolumeFrozenSpec` (det/log tensor and rescale laws, hull average sandwich)
and proves `hullDeterminantLogVolumeFrozenSpec_holds` from the Volume.lean packet lemmas.

This file gives the consumer-facing projections of that frozen spec: the packet
log-volume tensor/rescale laws and the hull average sandwich as standalone statements,
plus the holds-instance witness.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddHullFrozenSpecConsumerActualAdapted

open LeanFormal.IUT
open scoped BigOperators

/-- **PROVED consumer:** frozen spec => packet log-volume tensor law. -/
theorem frozen_spec_log_tensor (h : HullDeterminantLogVolumeFrozenSpec)
    {α β : Type*} [Fintype α] [Fintype β] (p : PositivePacket α) (q : PositivePacket β) :
    packetLogVolume (tensorPacket p q) =
      (Fintype.card β : ℝ) * packetLogVolume p +
        (Fintype.card α : ℝ) * packetLogVolume q :=
  h.log_tensor p q

/-- **PROVED consumer:** frozen spec => packet log-volume rescale law. -/
theorem frozen_spec_log_rescale (h : HullDeterminantLogVolumeFrozenSpec)
    {label : Type*} [Fintype label] (c : ℝ) (hc : 0 < c)
    (packet : PositivePacket label) :
    packetLogVolume (rescalePacket c hc packet) =
      (Fintype.card label : ℝ) * Real.log c + packetLogVolume packet :=
  h.log_rescale c hc packet

/-- **PROVED consumer:** frozen spec => hull average sandwich `data.average ≤ hull.hullVolume`
(Remark 3.9.5, (iii) at the finite-packet interface). -/
theorem frozen_spec_hull_average (h : HullDeterminantLogVolumeFrozenSpec)
    {label : Type*} [Fintype label] (hull : FiniteHull label)
    (data : WeightedValues label)
    (hvalue : ∀ i, data.value i = hull.volume i)
    (hw : ∀ i, 0 ≤ data.weight i) :
    data.average ≤ hull.hullVolume :=
  h.hull_average hull data hvalue hw

/-- **PROVED:** the frozen hull/det spec is realized by the tree packet lemmas. -/
theorem frozen_spec_holds : HullDeterminantLogVolumeFrozenSpec :=
  hullDeterminantLogVolumeFrozenSpec_holds

/-- Row record: frozen-spec fields vs consumer projections. -/
def hullFrozenSpecRows : List (String × String × String) :=
  [ ("frozen spec definition (det/log tensor+rescale, hull average)", "REUSED DEF", "HullDeterminantLogVolumeReduction.HullDeterminantLogVolumeFrozenSpec")
  , ("frozen spec realized from packet lemmas", "REUSED PROVED", "hullDeterminantLogVolumeFrozenSpec_holds")
  , ("log tensor consumer", "COMPOSED PROVED", "frozen_spec_log_tensor")
  , ("log rescale consumer", "COMPOSED PROVED", "frozen_spec_log_rescale")
  , ("hull average sandwich consumer", "COMPOSED PROVED", "frozen_spec_hull_average") ]

theorem hullFrozenSpecRows_length : hullFrozenSpecRows.length = 5 := rfl

#check frozen_spec_log_tensor
#check frozen_spec_log_rescale
#check frozen_spec_hull_average
#check frozen_spec_holds
#check hullFrozenSpecRows_length

end LeanFormal.IUT.XiFPaper.ShehddHullFrozenSpecConsumerActualAdapted
end
