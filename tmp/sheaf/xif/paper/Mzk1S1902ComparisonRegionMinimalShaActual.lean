import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

/-!
# shehdd A625 minimal stable S1902 comparison region (Sha)

Rollback to the minimal stable object: the concrete comparison region from the
green raw S1902 IQ hull interface, with its definitional form and finiteness from
comparison data.  No bridge/ABC wiring here (canonical bridge is mainline's
`Mzk1S1902BridgeInterfaceActual`, green).

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1S1902ComparisonRegionMinimalShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.ABCBridge

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Minimal concrete S1902 comparison region. -/
noncomputable def minimalComparisonRegion
    (logShellPoint : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat) :
    Set (S1902Carrier T) :=
  normalizedComparisonRegion (s1902IQHullLogVolumeInterface T) logShellPoint a b c

theorem minimalComparisonRegion_eq
    (logShellPoint : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat) :
    minimalComparisonRegion T logShellPoint a b c =
      normalizedComparisonRegion (s1902IQHullLogVolumeInterface T) logShellPoint a b c :=
  rfl

theorem minimalComparisonRegion_is_comparisonRegion
    {epsilon : Real}
    (C : Cor312EpsilonArithmeticComparison (s1902IQHullLogVolumeInterface T) epsilon)
    (a b c : Nat) :
    minimalComparisonRegion T C.logShellPoint a b c = C.comparisonRegion a b c :=
  rfl

theorem minimalComparisonRegion_logVolume_lt_top
    {epsilon : Real}
    (C : Cor312EpsilonArithmeticComparison (s1902IQHullLogVolumeInterface T) epsilon) :
    ∀ a b c : Nat, IsABCTriple a b c →
      (s1902IQHullLogVolumeInterface T).logVolume (C.comparisonRegion a b c) < ⊤ :=
  C.comparisonRegion_logVolume_lt_top

end LeanFormal.IUT.XiFPaper.Mzk1S1902ComparisonRegionMinimalShaActual
