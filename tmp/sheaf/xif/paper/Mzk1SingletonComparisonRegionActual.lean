/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic
/-! # Singleton point subset of the normalized comparison region -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1SingletonComparisonRegionActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper
variable {X : Type*} (W : LeanFormal.IUT.IQHullLogVolumeInterface X)
   (logShellPoint : Nat → Nat → Nat → X) (a b c : Nat)
/-- The scaled singleton point lies in the normalized comparison region. -/
theorem singleton_subset_normalizedComparisonRegion :
    ({W.scaleShift (logShellPoint a b c)} : Set X) ⊆
      LeanFormal.IUT.normalizedComparisonRegion W logShellPoint a b c := by
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨logShellPoint a b c, Set.mem_union_right _ (Set.mem_singleton _), rfl⟩
/-- Volume monotonicity for the singleton comparison. -/
theorem singletonVolume_le_normalizedComparisonRegionVolume :
    W.logVolume ({W.scaleShift (logShellPoint a b c)} : Set X) ≤
      W.logVolume (LeanFormal.IUT.normalizedComparisonRegion W logShellPoint a b c) :=
  W.logVolume_mono (singleton_subset_normalizedComparisonRegion W logShellPoint a b c)
end LeanFormal.IUT.XiFPaper.Mzk1SingletonComparisonRegionActual
end