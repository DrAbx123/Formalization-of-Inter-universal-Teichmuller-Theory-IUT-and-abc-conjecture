import tmp.sheaf.xif.paper.Node09ComparisonCardsActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Node09ComparisonCardsActual

namespace LeanFormal.IUT.XiFPaper.Node09RegionMonoActual

universe u

/-- The scaled point singleton is a subset of the normalized comparison region. -/
theorem singleton_subset_normalizedComparisonRegion
    (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (a b c : Nat) :
    ({W.scaleShift (logShellPoint a b c)} : Set X) ⊆
      normalizedComparisonRegion W logShellPoint a b c := by
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact ⟨logShellPoint a b c,
    Set.mem_union_right _ (Set.mem_singleton _), rfl⟩

/-- Monotonicity form: the singleton volume is at most the region volume. -/
theorem singletonVolume_le_regionVolume
    (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (a b c : Nat) :
    W.logVolume {W.scaleShift (logShellPoint a b c)} ≤
      W.logVolume (normalizedComparisonRegion W logShellPoint a b c) :=
  W.logVolume_mono
    (singleton_subset_normalizedComparisonRegion X W logShellPoint a b c)

/-- The scaled point singleton is contained in the normalized comparison region. -/
theorem singletonVolume_le_normalizedComparisonRegion
    (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (a b c : Nat) :
    W.logVolume {W.scaleShift (logShellPoint a b c)} ≤
      W.logVolume (normalizedComparisonRegion W logShellPoint a b c) := by
  apply W.logVolume_mono
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact ⟨logShellPoint a b c,
    Set.mem_union_right _ (Set.mem_singleton _), rfl⟩

/-- Consequently a bound on the normalized comparison region volume bounds the
singleton volume, so comparison (1) of the degree-upper-bound route is removed. -/
theorem singleton_toReal_le_of_region_toReal_le
    (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (a b c : Nat) {Xb : Real}
    (hfin : W.logVolume (normalizedComparisonRegion W logShellPoint a b c) < ⊤)
    (hregion : (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal ≤ Xb) :
    (W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal ≤ Xb :=
  le_trans
    (ENNReal.toReal_mono (ne_of_lt hfin)
      (singletonVolume_le_normalizedComparisonRegion X W logShellPoint a b c))
    hregion

/-- Exact residual after removing the singleton-to-region comparison. -/
def Node09RegionMonoResidual : List String :=
  [ "singleton <= normalizedComparisonRegion is proved by logVolume_mono and the definition normalizedComparisonRegion = scaleShift '' (unitRegion ∪ {point})",
    "therefore hdegreeBound/hsingleton_le_weight follows from a region-volume bound (normalizedComparisonRegion volume).toReal <= (1+eps)*arithmeticWeight + D1 plus region finiteness; the singleton-to-product comparison (1) is no longer needed",
    "remaining paper-level input: the normalized comparison-region volume <= weighted arithmetic bound (IUT IV main log-volume estimate); no donor in the current tree",
    "no inhabitant is constructed; this file only removes comparison (1) by monotonicity" ]

end LeanFormal.IUT.XiFPaper.Node09RegionMonoActual
