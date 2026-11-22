/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-! # A617/A625/A626: concrete S1902 comparison region — minimal stable version

The actual S1902 hull interface has `scaleShift = id` and unit region
`s1902UnitRegion T` (product unit ball).  Therefore its `normalizedComparisonRegion`
is the *unscaled* region

  `comparisonRegion T point a b c = s1902UnitRegion T ∪ {point a b c}`.

This is the minimal stable fixed-scale shape; the paper height comparison needs the
triple-dependent scaling (see `Mzk1PaperComparisonRegionScalingActual`), so these
definitions are alignment data only, not an estimate.  ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1S1902ComparisonRegionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual S1902 comparison region: the unscaled unit region plus the point datum. -/
noncomputable def comparisonRegion (point : Nat → Nat → Nat → S1902Carrier T)
    (a b c : Nat) : Set (S1902Carrier T) :=
  normalizedComparisonRegion (s1902IQHullLogVolumeInterface T) point a b c

/-- The actual interface has `scaleShift = id`, so the region is the unscaled
`unitRegion ∪ {point}`. -/
theorem comparisonRegion_eq_unscaled (point : Nat → Nat → Nat → S1902Carrier T)
    (a b c : Nat) :
    comparisonRegion T point a b c =
      s1902UnitRegion T ∪ ({point a b c} : Set (S1902Carrier T)) := by
  simp [comparisonRegion, normalizedComparisonRegion, s1902IQHullLogVolumeInterface,
    s1902UnitRegion, s1902ScaleShift]

/-- When the point lies in the unit region, the region collapses to the unit region. -/
theorem comparisonRegion_eq_unitRegion_of_mem
    (point : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat)
    (h : point a b c ∈ s1902UnitRegion T) :
    comparisonRegion T point a b c = s1902UnitRegion T := by
  rw [comparisonRegion_eq_unscaled, Set.union_singleton, Set.insert_eq_of_mem h]

/-- The q-pilot image point lies in the actual hull (re-export for consumers). -/
theorem qPilot_mem_hull : qPilotInThetaCarrier T ∈ s1902Hull T :=
  qPilotInThetaCarrier_mem_hull T

def comparisonRegionRows : List (String × String × String) :=
  [ ("comparison region definition", "comparisonRegion", "DEF (scaled region)"),
    ("unscaled identity", "comparisonRegion_eq_unscaled", "PROVED"),
    ("unit-region collapse", "comparisonRegion_eq_unitRegion_of_mem", "PROVED"),
    ("q-pilot hull containment", "qPilot_mem_hull", "PROVED"),
    ("scope", "alignment only; triple scaling in paper-region file", "INTEGRITY") ]

theorem comparisonRegionRows_length : comparisonRegionRows.length = 5 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1902ComparisonRegionActual.comparisonRegion_eq_unscaled
#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1902ComparisonRegionActual.comparisonRegion_eq_unitRegion_of_mem

end LeanFormal.IUT.XiFPaper.Mzk1S1902ComparisonRegionActual

end