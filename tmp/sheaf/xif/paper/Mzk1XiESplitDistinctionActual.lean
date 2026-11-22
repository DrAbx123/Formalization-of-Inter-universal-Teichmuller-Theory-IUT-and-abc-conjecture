import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-!
# A537: q_in_possible (rfl) vs possible_in_hull (genuine xi-e) distinction

In the current final assembly `xiERequirementOfGenuine` has
`qRegion = thetaPossibleImages = {qPilotInThetaCarrier T}` and therefore
`q_in_possible := subset_rfl` is a DEFINITIONAL identification, while
`possible_in_hull : {qPilotInThetaCarrier T} ⊆ s1902Hull T` is the GENUINE step
(proved from the SHE root relation + norm/radius bound).  This file records the
distinction explicitly and flags that a genuinely two-sided xi-e containment
requires a non-singleton `thetaPossibleImages` family (actual LANA possibleRegion
of the Theta raw output), not `qRegion = thetaPossibleImages`.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1XiESplitDistinctionActual

open LeanFormal.IUT

/-- A split xi-e containment: q region inside the Theta possible images, and
possible images inside the hull. -/
structure XiESplit (α : Type*) where
  qRegion : Set α
  thetaPossibleImages : Set α
  hullRegion : Set α
  q_in_possible : Set.Subset qRegion thetaPossibleImages
  possible_in_hull : Set.Subset thetaPossibleImages hullRegion

/-- If `qRegion = thetaPossibleImages`, the `q_in_possible` field is definitional
(rfl) and carries no mathematical content. -/
theorem q_in_possible_trivial_of_eq {α : Type*} (D : XiESplit α)
    (h : D.qRegion = D.thetaPossibleImages) :
    Set.Subset D.qRegion D.thetaPossibleImages :=
  h.le

/-- If `thetaPossibleImages = hullRegion`, the `possible_in_hull` field is
definitional (rfl) and carries no mathematical content. -/
theorem possible_in_hull_trivial_of_eq {α : Type*} (D : XiESplit α)
    (h : D.thetaPossibleImages = D.hullRegion) :
    Set.Subset D.thetaPossibleImages D.hullRegion :=
  h.le

/-- Genuine two-sided content: the q region, the possible-image family and the
hull are pairwise distinct sets (strict inclusions on both sides). -/
structure GenuineXiESplit (α : Type*) extends XiESplit α where
  q_neq_possible : qRegion ≠ thetaPossibleImages
  possible_neq_hull : thetaPossibleImages ≠ hullRegion

/-- The genuine data compose to the containment used by the signed comparison. -/
theorem genuine_containment {α : Type*} (D : GenuineXiESplit α) :
    Set.Subset D.qRegion D.hullRegion :=
  Set.Subset.trans D.q_in_possible D.possible_in_hull

end LeanFormal.IUT.XiFPaper.Mzk1XiESplitDistinctionActual
