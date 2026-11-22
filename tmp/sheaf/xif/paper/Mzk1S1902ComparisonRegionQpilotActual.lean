/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1S1902ConcreteBridgeQpilotActual
import Mathlib.Tactic

/-! # Mzk1S1902ComparisonRegionQpilotActual — S1902 comparison region (A614)

The concrete comparison region on the S1902 hull data: `normalizedComparisonRegion`
specialized to `s1902IQHullLogVolumeInterface`, with its equality form and the
derived finiteness under comparison data. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1S1902ComparisonRegionQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1S1902ConcreteBridgeQpilotActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The concrete S1902 comparison region. -/
noncomputable def s1902ComparisonRegion
    (logShellPoint : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat) :
    Set (S1902Carrier T) :=
  normalizedComparisonRegion (s1902IQHullLogVolumeInterface T) logShellPoint a b c

/-- Definitional form of the S1902 comparison region. -/
theorem s1902ComparisonRegion_eq
    (logShellPoint : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat) :
    s1902ComparisonRegion T logShellPoint a b c =
      normalizedComparisonRegion (s1902IQHullLogVolumeInterface T) logShellPoint a b c :=
  rfl

/-- Finiteness of the S1902 comparison-region log-volume from comparison data. -/
theorem s1902ComparisonRegion_logVolume_lt_top
    {epsilon : Real}
    (C : Cor312EpsilonArithmeticComparison (s1902IQHullLogVolumeInterface T) epsilon) :
    ∀ a b c : Nat, IsABCTriple a b c →
      (s1902IQHullLogVolumeInterface T).logVolume
        (C.comparisonRegion a b c) < ⊤ :=
  C.comparisonRegion_logVolume_lt_top

/-- The S1902 comparison region is the accessor region of the comparison data. -/
theorem s1902ComparisonRegion_comparisonRegion
    {epsilon : Real}
    (C : Cor312EpsilonArithmeticComparison (s1902IQHullLogVolumeInterface T) epsilon)
    (a b c : Nat) :
    s1902ComparisonRegion T C.logShellPoint a b c = C.comparisonRegion a b c :=
  rfl

#check s1902ComparisonRegion
#check s1902ComparisonRegion_logVolume_lt_top

end LeanFormal.IUT.XiFPaper.Mzk1S1902ComparisonRegionQpilotActual
end
