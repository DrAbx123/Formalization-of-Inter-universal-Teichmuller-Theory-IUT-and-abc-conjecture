/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual

/-! # A617 hull: canonical S1902 `IQHullLogVolumeInterface` — thin re-export

The canonical concrete instance is already GREEN in
`S1902ActualThetaHullActual.s1902IQHullLogVolumeInterface` (all fields proved:
`s1902ImageSet` / `s1902Hull` / `s1902LogVolume` / `s1902UnitRegion` /
`s1902ScaleShift`).  This module is a thin re-export under the A615 canonical
name; no instance is rebuilt, no new mathematics, no named field. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1S1902IQHullInterfaceCanonicalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- A615 canonical concrete `IQHullLogVolumeInterface` on the S1902 carrier. -/
noncomputable def s1902IQHullInterfaceCanonical :
    IQHullLogVolumeInterface (S1902Carrier T) :=
  s1902IQHullLogVolumeInterface (T := T)

/-- rfl check: the canonical image set is the actual s1902 image set. -/
theorem canonical_imageSet :
    (s1902IQHullInterfaceCanonical T).imageSet = s1902ImageSet T := rfl

/-- rfl check: the canonical hull is the actual s1902 hull. -/
theorem canonical_hull :
    (s1902IQHullInterfaceCanonical T).hull = s1902Hull T := rfl

/-- The canonical instance's hull log-volume is finite (paper-level conclusion). -/
theorem canonical_hull_logVolume_lt_top :
    (s1902IQHullInterfaceCanonical T).logVolume (s1902IQHullInterfaceCanonical T).hull < ⊤ :=
  (s1902IQHullInterfaceCanonical T).hull_logVolume_lt_top

def canonicalRows : List (String × String × String) :=
  [ ("canonical instance", "s1902IQHullLogVolumeInterface (green)", "GREEN"),
    ("imageSet/hull rfl", "canonical_imageSet/canonical_hull", "PROVED (rfl)"),
    ("hull finiteness", "canonical_hull_logVolume_lt_top", "PROVED") ]

theorem canonicalRows_length : canonicalRows.length = 3 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1902IQHullInterfaceCanonicalActual.s1902IQHullInterfaceCanonical
#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1902IQHullInterfaceCanonicalActual.canonical_hull_logVolume_lt_top

end LeanFormal.IUT.XiFPaper.Mzk1S1902IQHullInterfaceCanonicalActual

end