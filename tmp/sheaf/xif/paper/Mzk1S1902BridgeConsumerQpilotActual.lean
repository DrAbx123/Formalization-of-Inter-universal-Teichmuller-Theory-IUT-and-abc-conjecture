/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1S1902ComparisonRegionQpilotActual
import tmp.sheaf.xif.paper.Mzk1HeightEstimateQpilotActual
import Mathlib.Tactic

/-! # Mzk1S1902BridgeConsumerQpilotActual — S1902 bridge/estimate consumer

A616 (qpilot lane, supplementary): the concrete S1902 hull data is fed through the
bridge and the height-estimate chain:
* `s1902_bridge_heightBound`: concrete bridge consumer;
* `s1902_height_estimate`: the `(1+3ε)` height estimate on the S1902 carrier;
* `s1902_hull_finite`: paper hull finiteness for the concrete S1902 data. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1S1902BridgeConsumerQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1S1902ConcreteBridgeQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1S1902ComparisonRegionQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1HeightEstimateQpilotActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Concrete S1902 bridge height bound. -/
theorem s1902_bridge_heightBound
    (C : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison (s1902IQHullLogVolumeInterface T) epsilon) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  s1902Bridge_heightBound T C

/-- The `(1+3ε)` height estimate on the S1902 carrier. -/
theorem s1902_height_estimate {epsilon : Real}
    (C : Cor312EpsilonArithmeticComparison (s1902IQHullLogVolumeInterface T) epsilon)
    (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + 3 * epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (1 + epsilon) *
            (((s1902IQHullLogVolumeInterface T).logVolume
              (s1902IQHullLogVolumeInterface T).hull).toReal + D) :=
  height_estimate C h0 h1

/-- Paper hull finiteness on the concrete S1902 data. -/
theorem s1902_hull_finite :
    (s1902IQHullLogVolumeInterface T).logVolume
      (s1902IQHullLogVolumeInterface T).hull < ⊤ :=
  s1902Bridge_hull_finite T

#check s1902_bridge_heightBound
#check s1902_height_estimate
#check s1902_hull_finite

end LeanFormal.IUT.XiFPaper.Mzk1S1902BridgeConsumerQpilotActual
end
