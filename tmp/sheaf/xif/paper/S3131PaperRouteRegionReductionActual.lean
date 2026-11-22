import Mathlib
import tmp.sheaf.xif.paper.S3131PaperRouteFieldStatementsActual

/-! # S3131 paper route: (c) reduction — UNDILATED region-volume bound implies (c)

(c) is `forall eps>0, exists D, ....`  The (1+eps) dilation is bookkeeping given
arithmeticWeight >= 0.  The undilated bound is the IV section 2 / [GenEll] estimate
(NOT formalized in tree: explicit hypothesis). -/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual

namespace LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual

universe u

/-- UNDILATED region-volume strength bound: the exact arithmetic input needed for (c). -/
def UndilatedRegionBound {X : Type u} (W : IQHullLogVolumeInterface X)
    (pt : Nat → Nat → Nat → X) : Prop :=
  ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
    (W.logVolume {pt a b c}).toReal ≤
      arithmeticWeight (abcRationalPoint a c) + (W.logVolume W.hull).toReal + D

/-- Raw form: an explicit constant D gives the region-volume family. -/
theorem regionVolumeFamily_of_raw {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X} {D : Real}
    (hD : ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume {pt a b c}).toReal ≤
        arithmeticWeight (abcRationalPoint a c) + (W.logVolume W.hull).toReal + D) :
    RegionVolumeFamily W pt := by
  unfold RegionVolumeFamily
  intro eps heps
  refine ⟨D, ?_⟩
  intro a b c habc
  have h1 := hD a b c habc
  have hw : (0 : Real) ≤ arithmeticWeight (abcRationalPoint a c) := arithmeticWeight_nonneg _
  have hdil := mul_le_mul_of_nonneg_right (by linarith : (1 : Real) ≤ 1 + eps) hw
  linarith

/-- **PROVABLE reduction:** the undilated arithmetic bound implies field (c). -/
theorem regionVolumeFamily_of_undilated {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (h : UndilatedRegionBound W pt) : RegionVolumeFamily W pt := by
  unfold UndilatedRegionBound at h
  rcases h with ⟨D, hD⟩
  exact regionVolumeFamily_of_raw (D := D) hD

#check regionVolumeFamily_of_undilated

end LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual
end