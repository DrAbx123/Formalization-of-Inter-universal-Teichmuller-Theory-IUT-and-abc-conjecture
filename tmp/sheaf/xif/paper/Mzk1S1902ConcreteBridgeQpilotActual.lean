/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual

/-! # Mzk1S1902ConcreteBridgeQpilotActual — concrete bridge on the S1902 hull data

A614 (qpilot lane): the green concrete `IQHullLogVolumeInterface` instance
`s1902IQHullLogVolumeInterface` (actual S1902 image/hull/log-volume/unit region)
is used as the bridge `hullData`; supplied per-ε comparison data then give a
concrete `Cor312ToABCBridgeInterface` and the bridge height bound. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1S1902ConcreteBridgeQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Concrete bridge over the S1902 hull data from a per-`ε` comparison family. -/
noncomputable def s1902BridgeOfComparisons
    (C : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison (s1902IQHullLogVolumeInterface T) epsilon) :
    Cor312ToABCBridgeInterface.{0} where
  carrier := S1902Carrier T
  hullData := s1902IQHullLogVolumeInterface T
  epsilonComparison := C

/-- Concrete bridge height bound (green bridge consumer applied to the S1902 bridge). -/
theorem s1902Bridge_heightBound
    (C : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison (s1902IQHullLogVolumeInterface T) epsilon) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312ToABCBridge_heightBound (s1902BridgeOfComparisons T C)

/-- The S1902 bridge inherits the paper hull finiteness from the concrete data. -/
theorem s1902Bridge_hull_finite :
    (s1902IQHullLogVolumeInterface T).logVolume
      (s1902IQHullLogVolumeInterface T).hull < ⊤ :=
  IQHullLogVolumeInterface.hull_logVolume_lt_top (s1902IQHullLogVolumeInterface T)

#check s1902BridgeOfComparisons
#check s1902Bridge_heightBound
#check s1902Bridge_hull_finite

end LeanFormal.IUT.XiFPaper.Mzk1S1902ConcreteBridgeQpilotActual
end
