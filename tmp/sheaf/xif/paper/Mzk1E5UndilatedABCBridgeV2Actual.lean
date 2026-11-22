import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual
import tmp.sheaf.xif.paper.S3171UniformHeightConsumerActual
import tmp.sheaf.xif.paper.S3131PaperRouteSkeletonActual
import tmp.sheaf.xif.paper.S3131PaperRouteFieldStatementsActual
import tmp.sheaf.xif.paper.S3131PaperRouteHeightReductionActual
import tmp.sheaf.xif.paper.S3131PaperRouteRegionReductionActual
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

/-! Mainline: E-5 clean consumer — the two named IUT IV inputs (b) UndilatedHeightBound
  and (c) UndilatedRegionBound imply ABCConjecture through the proved undilated route. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1E5UndilatedABCBridgeV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteSkeletonActual
open LeanFormal.IUT.XiFPaper.S3171UniformHeightConsumerActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual

universe u

/-- (b)+(c) as named paper inputs yield ABCConjecture (proved consumer). -/
theorem abcConjecture_of_undilatedBounds {X : Type u} {W : IQHullLogVolumeInterface X}
    {pt : Nat → Nat → Nat → X}
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    ABCConjecture :=
  abcConjecture_of_undilated hb hc

/-- (b) alone gives the height-comparison family (re-export of the reduction). -/
theorem heightComparisonFamily_of_undilatedBound {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (h : UndilatedHeightBound W pt) : HeightComparisonFamily W pt :=
  heightComparisonFamily_of_undilated h

/-- (c) alone gives the region-volume family (re-export of the reduction). -/
theorem regionVolumeFamily_of_undilatedBound {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (h : UndilatedRegionBound W pt) : RegionVolumeFamily W pt :=
  regionVolumeFamily_of_undilated h

/-- The residual-data bundle of the paper route from (b)+(c) (`PaperRouteResidualData W`
  is Type data; the point datum is a field of the residual data). -/
def paperRouteResidualData_of_undilatedBounds {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    PaperRouteResidualData W :=
  paperRouteResidualData_of_undilated hb hc

/-- The residual-data bundle is inhabited whenever (b)+(c) hold (Prop-level form). -/
theorem nonempty_paperRouteResidualData_of_undilatedBounds {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    Nonempty (PaperRouteResidualData W) :=
  ⟨paperRouteResidualData_of_undilatedBounds hb hc⟩

/-- (b)+(c) via the paper-route residual skeleton gives ABC. -/
theorem abcConjecture_of_undilatedBounds_via_residuals {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    ABCConjecture :=
  abcConjecture_of_paperRouteResiduals (paperRouteResidualData_of_undilatedBounds hb hc)

/-- Uniform valuation bound + volume dominance gives (b) UndilatedHeightBound:
  the uniform valuation bound yields the weighted height bound, and volume dominance
  turns it into the undilated height/volume bound. -/
theorem undilatedHeightBound_of_valuation_bound_re {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X} {B : ℝ}
    (hbound : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ p ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat p (abcRationalPoint a c) : ℝ)) ≤ B)
    (hvol : ∀ a b c : Nat, IsABCTriple a b c →
      B * arithmeticWeight (abcRationalPoint a c) ≤
        (W.logVolume {pt a b c}).toReal) :
    UndilatedHeightBound W pt := by
  intro a b c habc
  have h1 := abcRationalPoint_logHeight₁_le_mul_arithmeticWeight_of_uniform_valuation_bound
    habc (hbound a b c habc)
  have h2 := hvol a b c habc
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1E5UndilatedABCBridgeV2Actual
-- A484 retry: forced mtime refresh after stale-content compile race.
