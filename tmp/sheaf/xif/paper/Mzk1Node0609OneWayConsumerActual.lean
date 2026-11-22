/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarProductStrictMainlineActual
import tmp.sheaf.xif.paper.Node09HqMultConsumerActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import Mathlib.Tactic
/-! # node06/09 one-way consumer from the strict product-region bound -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Node0609OneWayConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual
open LeanFormal.IUT.XiFPaper.Node09HqMultConsumerActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open MeasureTheory
open scoped BigOperators ENNReal
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]
/-- One-way strict bound: rpRegion volume < actual theta hull volume. -/
theorem node0609_rpRegion_volume_lt_hull :
    rpVolume T (rpRegion T) < rpVolume T (s1902Hull T) :=
  rp_strict_measure_resolved T
/-- One-way non-strict bound for downstream consumers. -/
theorem node0609_rpRegion_volume_le_hull :
    rpVolume T (rpRegion T) ≤ rpVolume T (s1902Hull T) :=
  le_of_lt (node0609_rpRegion_volume_lt_hull T)
def rows : List (String × String) :=
  [ ("strict volume", "PROVED: rpRegion < hull via rp_strict_measure_resolved"),
    ("non-strict", "PROVED: rpRegion ≤ hull"),
    ("weighted q identification", "MISSING: rpVolume bound -> fiberMult weighted sum") ]
theorem rows_length : rows.length = 3 := rfl
#check node0609_rpRegion_volume_lt_hull
#check node0609_rpRegion_volume_le_hull
end LeanFormal.IUT.XiFPaper.Mzk1Node0609OneWayConsumerActual
end