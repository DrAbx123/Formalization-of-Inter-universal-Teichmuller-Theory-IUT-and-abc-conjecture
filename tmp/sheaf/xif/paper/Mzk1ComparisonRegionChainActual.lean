import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-! Mainline: structural chain lemmas for the normalized comparison region
  (real subset facts used by region-volume consumers). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ComparisonRegionChainActual

open LeanFormal.IUT

universe u

theorem scaleShift_unitRegion_subset_normalizedComparisonRegion
    {X : Type u} (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (a b c : Nat) :
    W.scaleShift '' W.unitRegion ⊆
      normalizedComparisonRegion W logShellPoint a b c := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, Set.mem_union_left _ hx, rfl⟩

theorem scaleShift_logShellPoint_subset_normalizedComparisonRegion
    {X : Type u} (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (a b c : Nat) :
    {W.scaleShift (logShellPoint a b c)} ⊆
      normalizedComparisonRegion W logShellPoint a b c := by
  rintro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact ⟨logShellPoint a b c, Set.mem_union_right _ (Set.mem_singleton _), rfl⟩

theorem normalizedComparisonRegion_unfold
    {X : Type u} (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (a b c : Nat) :
    normalizedComparisonRegion W logShellPoint a b c =
      W.scaleShift '' (W.unitRegion ∪ {logShellPoint a b c}) :=
  rfl

end LeanFormal.IUT.XiFPaper.Mzk1ComparisonRegionChainActual