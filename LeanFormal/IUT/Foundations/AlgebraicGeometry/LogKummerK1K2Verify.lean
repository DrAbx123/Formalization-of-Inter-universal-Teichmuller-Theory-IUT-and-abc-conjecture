import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogKummerK1K2
import Mathlib.Tactic

/-!
# Independent consumer check for LogKummerK1K2

This file only checks the generic statement for an arbitrary finite place at a
prime. It does not introduce any source card, Q5 constant, Noetherian/local
hypothesis, or cardinality invertibility assumption.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.N8.LogCarrierK1K2
open ABCBridge.LogKummerK1K2

namespace ABCBridge.LogKummerK1K2Verify

universe u

variable {F : Type u} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]
  (place : FinitePlaceAtPrime F p)

/-- Generic principal-unit log-Kummer naturality square. -/
example (u : principalUnits (K := SourceCompletion place)) :
    completionIsometryEquiv place
        (LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
          (K := SourceCompletion place) u) =
      LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
        (K := TargetCompletion place) (principalUnitMap place u) :=
  principalUnitLog_naturality place u

/-- Generic image-compatibility consumer formula. -/
example (u : principalUnits (K := SourceCompletion place)) :
    completionIsometryEquiv place
        (LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
          (K := SourceCompletion place) u) ∈
      Set.range (fun v : principalUnits (K := TargetCompletion place) =>
        LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
          (K := TargetCompletion place) v) :=
  principalUnitLog_image_compat place u

/-- Generic actual log-shell consumer formula. -/
example :
    (completionLogShell place.val : Set (Completion place.val)) =
      Set.range (fun u : (CompletionIntegers place.val)ˣ =>
        (logShellScale (completionRationalPrime place.val).val :
          Completion place.val)⁻¹ * completionUnitLog place.val u) :=
  completionLogShell_image_compat place

end ABCBridge.LogKummerK1K2Verify

#print axioms ABCBridge.LogKummerK1K2.principalUnitLog_naturality
#print axioms ABCBridge.LogKummerK1K2.principalUnitLog_image_compat
#print axioms ABCBridge.LogKummerK1K2.completionLogShell_image_compat