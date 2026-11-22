import tmp.sheaf.xif.paper.Cor312ComparisonRegionV2Actual

/-! # S3131 paper-route: exact (b)/(c) field statements (IUT IV Thm 1.10 shape / IV §2) -/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual

namespace LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual

universe u

/-- (b) Height comparison family: height of an ABC triple is bounded by the
(1+eps)-dilated log-volume of the comparison region (IUT IV Thm 1.10 shape). -/
def HeightComparisonFamily {X : Type u} (W : IQHullLogVolumeInterface X)
    (pt : Nat → Nat → Nat → X) : Prop :=
  ∀ ε : Real, 0 < ε → ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + ε) * (W.logVolume {pt a b c}).toReal

/-- (c) Region-volume strength family: comparison-region log-volume is bounded by
(1+eps)*arithmeticWeight + hull volume + a constant (IV §2 / [GenEll] strength). -/
def RegionVolumeFamily {X : Type u} (W : IQHullLogVolumeInterface X)
    (pt : Nat → Nat → Nat → X) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ D : Real,
    ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume {pt a b c}).toReal ≤
        (1 + ε) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D

#check HeightComparisonFamily
#check RegionVolumeFamily

end LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual
end