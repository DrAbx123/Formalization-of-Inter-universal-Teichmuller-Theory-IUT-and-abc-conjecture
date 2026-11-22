import tmp.sheaf.xif.paper.S3131PaperRouteRegionReductionActual
import tmp.sheaf.xif.paper.S3131PaperRouteHeightReductionActual
import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1E5RegionConsumerActual — E-5 (c) region consumer: undilated region -> (c) -> ABC

DAG node: e-deep:E5 (c) region component.  Exposes the proved reduction
UndilatedRegionBound -> RegionVolumeFamily and the combined (b)+(c) -> ABC route.
The undilated bounds remain explicit named inputs; no closure claim.
GATE NOT PASSED; registry 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1E5RegionConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual

universe u

/-- Undilated region bound -> (c) family (re-export). -/
theorem regionVolumeFamily_of_undilatedBound {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (h : UndilatedRegionBound W pt) : RegionVolumeFamily W pt :=
  regionVolumeFamily_of_undilated h

/-- Undilated height bound -> (b) family (re-export). -/
theorem heightComparisonFamily_of_undilatedBound {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (h : UndilatedHeightBound W pt) : HeightComparisonFamily W pt :=
  heightComparisonFamily_of_undilated h

/-- Combined (b)+(c) -> ABC (re-export of the paper-route skeleton route). -/
theorem abcConjecture_of_undilatedBounds {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    ABCConjecture :=
  abcConjecture_of_undilated hb hc

/-- Rows: E-5 (c) consumer status. -/
def e5RegionRows : List (String × String × String) :=
  [ ("undilated region -> (c) family", "regionVolumeFamily_of_undilatedBound", "PROVED (conditional)"),
    ("undilated height -> (b) family", "heightComparisonFamily_of_undilatedBound", "PROVED (conditional)"),
    ("(b)+(c) -> ABC", "abcConjecture_of_undilatedBounds", "PROVED (conditional)"),
    ("named inputs", "UndilatedHeightBound / UndilatedRegionBound", "NAMED (not proved)"),
    ("scope", "no closure; gate NOT PASSED", "INTEGRITY") ]

theorem e5RegionRows_length : e5RegionRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1E5RegionConsumerActual

end
