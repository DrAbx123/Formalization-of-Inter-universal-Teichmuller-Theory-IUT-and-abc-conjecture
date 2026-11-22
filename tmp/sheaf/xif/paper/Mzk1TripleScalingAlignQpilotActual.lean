/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1TripleScalingSpecQpilotActual
import tmp.sheaf.xif.paper.Mzk1S1902ComparisonRegionQpilotActual
import Mathlib.Tactic

/-! # Mzk1TripleScalingAlignQpilotActual — triple-dependent region alignment

A625 (qpilot supplementary): aligns the `TripleScalingSpec` region with the
bridge `normalizedComparisonRegion` on the green S1902 hull data:
`region a b c = scaleShift '' (unitRegion ∪ {pt a b c})` with
`scaleShift` from the interface. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1TripleScalingAlignQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1TripleScalingSpecQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1S1902ComparisonRegionQpilotActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The bridge-compatible triple scaling spec: `scale` is the interface's
`scaleShift`, and the region is the bridge `normalizedComparisonRegion`. -/
noncomputable def bridgeScalingSpec
    (pt : Nat → Nat → Nat → S1902Carrier T) : TripleScalingSpec T where
  pt := pt
  scale := fun _ _ _ => (s1902IQHullLogVolumeInterface T).scaleShift
  region := fun a b c =>
    normalizedComparisonRegion (s1902IQHullLogVolumeInterface T) pt a b c
  region_eq := by
    intro a b c
    rfl

/-- Alignment: the bridge-compatible spec region is the explicit scaled union. -/
theorem bridgeScalingSpec_region_eq (pt : Nat → Nat → Nat → S1902Carrier T)
    (a b c : Nat) :
    (bridgeScalingSpec T pt).region a b c =
      (s1902IQHullLogVolumeInterface T).scaleShift ''
        ((s1902IQHullLogVolumeInterface T).unitRegion ∪ {pt a b c}) :=
  rfl

/-- Alignment with the comparison-data accessor region. -/
theorem bridgeScalingSpec_comparisonRegion
    {epsilon : Real}
    (C : Cor312EpsilonArithmeticComparison (s1902IQHullLogVolumeInterface T) epsilon)
    (a b c : Nat) :
    (bridgeScalingSpec T C.logShellPoint).region a b c = C.comparisonRegion a b c :=
  rfl

#check bridgeScalingSpec
#check bridgeScalingSpec_region_eq
#check bridgeScalingSpec_comparisonRegion

end LeanFormal.IUT.XiFPaper.Mzk1TripleScalingAlignQpilotActual
end
