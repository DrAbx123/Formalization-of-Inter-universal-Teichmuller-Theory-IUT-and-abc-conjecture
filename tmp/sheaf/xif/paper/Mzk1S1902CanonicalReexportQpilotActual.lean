/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1S1902IQHullInterfaceActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

/-! # Mzk1S1902CanonicalReexportQpilotActual — canonical IQ hull re-export

A620 (qpilot lane, thin re-export): the canonical hull-side S1902 IQ interface
`s1902IQHullInterface` is re-exported and used as bridge `hullData`; the canonical
6-row audit table is re-exported.  Canonical file itself is hull-owned and untouched. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1S1902CanonicalReexportQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1S1902IQHullInterfaceActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- Re-export: the canonical S1902 IQ hull interface. -/
noncomputable def canonicalIQHull [Fintype (Bad (nativePlaceSelection T))] :
    IQHullLogVolumeInterface (S1902Carrier T) := by
  haveI : Nonempty (Bad (nativePlaceSelection T)) := bad_nonempty T
  exact s1902IQHullInterface T

/-- Re-export: canonical hull log-volume finiteness. -/
theorem canonicalIQHull_finite [Fintype (Bad (nativePlaceSelection T))] :
    (canonicalIQHull T).logVolume (canonicalIQHull T).hull < ⊤ :=
  IQHullLogVolumeInterface.hull_logVolume_lt_top (canonicalIQHull T)

/-- Re-export: the canonical 6-row audit table length. -/
theorem canonicalIQHull_rows_length : (s1902IQHullRows).length = 6 :=
  s1902IQHullRows_length

/-- Concrete bridge over the CANONICAL hull data from a per-`ε` comparison family. -/
noncomputable def canonicalBridgeOfComparisons [Fintype (Bad (nativePlaceSelection T))]
    (C : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison (canonicalIQHull T) epsilon) :
    Cor312ToABCBridgeInterface.{0} where
  carrier := S1902Carrier T
  hullData := canonicalIQHull T
  epsilonComparison := C

/-- Bridge height bound on the canonical hull data. -/
theorem canonicalBridge_heightBound [Fintype (Bad (nativePlaceSelection T))]
    (C : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison (canonicalIQHull T) epsilon) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312ToABCBridge_heightBound (canonicalBridgeOfComparisons T C)

#check canonicalIQHull
#check canonicalIQHull_finite
#check canonicalBridge_heightBound

end LeanFormal.IUT.XiFPaper.Mzk1S1902CanonicalReexportQpilotActual
end
