import Mathlib
import tmp.sheaf.xif.paper.S3131PaperRouteFieldStatementsActual

/-! # S3131 route: comparison-invariance residual (named; NOT automatic) -/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual

namespace LeanFormal.IUT.XiFPaper.S3131RouteComparisonInvarianceActual

universe u

def S3131RouteComparisonInvariance {X : Type u} (W : IQHullLogVolumeInterface X)
    (f : X → X) : Prop :=
  ∀ S : Set X, W.logVolume (f '' S) = W.logVolume S

def imageRegion {X : Type u} (f : X → X) (pt : Nat → Nat → Nat → X) :
    Nat → Nat → Nat → Set X := fun a b c => f '' ({pt a b c} : Set X)

/-- PROVABLE transfer of (b) to the image region under the named invariance residual. -/
theorem heightComparisonFamily_image {X : Type u} {W : IQHullLogVolumeInterface X}
    {f : X → X} {pt : Nat → Nat → Nat → X}
    (hinv : S3131RouteComparisonInvariance W f) (hh : HeightComparisonFamily W pt) :
    ∀ eps : Real, 0 < eps → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * (W.logVolume (imageRegion f pt a b c)).toReal := by
  intro eps heps a b c habc
  have h := hh eps heps a b c habc
  have hv : W.logVolume (imageRegion f pt a b c) = W.logVolume {pt a b c} := by
    unfold imageRegion
    exact hinv {pt a b c}
  rw [hv]
  exact h

/-- PROVABLE transfer of (c) to the image region under the named invariance residual. -/
theorem regionVolumeFamily_image {X : Type u} {W : IQHullLogVolumeInterface X}
    {f : X → X} {pt : Nat → Nat → Nat → X}
    (hinv : S3131RouteComparisonInvariance W f) (hr : RegionVolumeFamily W pt) :
    ∀ eps : Real, 0 < eps → ∃ D : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        (W.logVolume (imageRegion f pt a b c)).toReal ≤
          (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
            (W.logVolume W.hull).toReal + D := by
  intro eps heps
  obtain ⟨D, hD⟩ := hr eps heps
  refine ⟨D, ?_⟩
  intro a b c habc
  have h := hD a b c habc
  have hv : W.logVolume (imageRegion f pt a b c) = W.logVolume {pt a b c} := by
    unfold imageRegion
    exact hinv {pt a b c}
  rw [hv]
  exact h

#check S3131RouteComparisonInvariance
#check heightComparisonFamily_image
#check regionVolumeFamily_image

end LeanFormal.IUT.XiFPaper.S3131RouteComparisonInvarianceActual
end