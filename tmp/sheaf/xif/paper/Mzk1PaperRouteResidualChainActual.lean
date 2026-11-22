import tmp.sheaf.xif.paper.S3131PaperRouteSkeletonActual
import tmp.sheaf.xif.paper.S3131PaperRouteHeightReductionActual
import tmp.sheaf.xif.paper.S3131PaperRouteRegionReductionActual

/-! Mainline: construct the S3131 paper-route residual data from the two UNDILATED
  analytic inputs (b)/(c), and derive ABC (new composition; real proofs). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperRouteResidualChainActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3131PaperRouteSkeletonActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual

universe u

/-- Build the forward residual data from the undilated (b)/(c) bounds. -/
def paperRouteResidualData_of_undilatedBounds {X : Type u}
    (W : IQHullLogVolumeInterface X) (pt : Nat → Nat → Nat → X)
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    PaperRouteResidualData W where
  point := pt
  height_comparison := by
    intro eps heps a b c habc
    have h1 := hb a b c habc
    have hv : (0 : Real) ≤ (W.logVolume {pt a b c}).toReal := ENNReal.toReal_nonneg
    have hdil : (W.logVolume {pt a b c}).toReal ≤
        (1 + eps) * (W.logVolume {pt a b c}).toReal := by nlinarith
    linarith
  region_volume_bound := by
    intro eps heps
    obtain ⟨D, hD⟩ := hc
    refine ⟨D, fun a b c habc => ?_⟩
    have h1 := hD a b c habc
    have hw : (0 : Real) ≤ arithmeticWeight (abcRationalPoint a c) :=
      arithmeticWeight_nonneg _
    have hdil := mul_le_mul_of_nonneg_right (by linarith : (1 : Real) ≤ 1 + eps) hw
    linarith

/-- New composition: undilated (b) + (c) give ABC via the paper-route residual data. -/
theorem abcConjecture_of_undilatedBounds_residual {X : Type u}
    (W : IQHullLogVolumeInterface X) (pt : Nat → Nat → Nat → X)
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    ABCConjecture :=
  abcConjecture_of_paperRouteResiduals
    (paperRouteResidualData_of_undilatedBounds W pt hb hc)

end LeanFormal.IUT.XiFPaper.Mzk1PaperRouteResidualChainActual