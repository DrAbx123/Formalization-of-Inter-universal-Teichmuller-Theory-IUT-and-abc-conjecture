import tmp.sheaf.xif.paper.S3131PaperRouteFieldStatementsActual

/-! # S3131 paper route: V2 comparison region REUSING prior-art normalizedComparisonRegion -/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual

namespace LeanFormal.IUT.XiFPaper.S3131PaperRouteV2RegionReuseActual

universe u

/-- Prior-art paper-style comparison region reused from the bridge interface file:
the `scaleShift`-image of the unit region together with the named point. -/
def S3131V2ComparisonRegion {X : Type u} (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (a b c : Nat) : Set X :=
  normalizedComparisonRegion W logShellPoint a b c

/-- The V2 field (a) for this region: point membership reduced to the named point
being in its own region under the prior-art construction (requires the point in the
scaleShift-image; recorded as a named membership hypothesis, not assumed). -/
def S3131V2RegionMembershipCondition {X : Type u} (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) : Prop :=
  ∀ a b c : Nat, logShellPoint a b c ∈ S3131V2ComparisonRegion W logShellPoint a b c

#check S3131V2ComparisonRegion
#check normalizedComparisonRegion

end LeanFormal.IUT.XiFPaper.S3131PaperRouteV2RegionReuseActual
end