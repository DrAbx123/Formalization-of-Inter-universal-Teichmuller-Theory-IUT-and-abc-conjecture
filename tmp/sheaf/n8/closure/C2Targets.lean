import tmp.sheaf.n8.closure.C2Native
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellActionCompatibility
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellXMuPacket
import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogKummerK1K2Consumer

/-!
# C2 target types for the native action/Kummer/K1K2/archimedean parts

Exact Lean target propositions for the four C2 native obligations.  Existing
production types are reused: SourceLogShellXMuChainActionCompatibility/Supply,
SourceLogShellXMuChainSupply, and the actual K1/K2 consumer.  No free Type or
True placeholder is used.

Each target has a theorem-level declaration: actual constructor where the
production theorem exists (K1/K2), named sorry where the production object is
missing (action, Kummer root-change, archimedean).
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C2Native
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.N8.LogCarrierK1K2
open ABCBridge.LogKummerK1K2

namespace LeanFormal.IUT.N8Closure.C2Targets

universe ua uv upi umon ui uG

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- One-index native log-shell family used to state the action obligation. -/
abbrev nativeDatum : Unit → SourceLogShellDatum :=
  fun _ => nativeLocalShell X

/-- Native G_v action target: an actual action/descent structure on the native
log-shell family, with the actual permutation group of native places.  The
chain supply is a parameter because production supplies it only conditionally. -/
def nativeGvActionTarget
    (S : SourceLogShellXMuChainSupply (nativeDatum X) (nativeDatum X) (nativeDatum X)) :
    Prop :=
  Nonempty (SourceLogShellXMuChainActionCompatibility (nativeDatum X) (nativeDatum X)
    (nativeDatum X) (Equiv.Perm (NativePlaces X.S)) S)

/-- Native Kummer/root-change target: the actual Kummer containment of the
native local shell.  The root-change map itself has no production type; the
exact missing declaration is recorded below. -/
def nativeKummerTarget : Prop :=
  (nativeLocalShell X).codomainKummerContained

/-- Native multi-place K1/K2 target: the actual per-completion K1/K2 log-Kummer
square, quantified over every finite place of the native base field. -/
def nativeK1K2Target : Prop :=
  ∀ (p : Nat) [Fact p.Prime]
    (place : FinitePlaceAtPrime (X.S.arithmetic.Fmod) p)
    (u : principalUnits (K := SourceCompletion place)),
      completionIsometryEquiv place
          (principalUnitLog (K := SourceCompletion place) u) =
        principalUnitLog (K := TargetCompletion place)
          (ABCBridge.LogKummerK1K2.principalUnitMap place u)

/-- Actual constructor: the production K1/K2 consumer proves the target for
every finite place, with no sorry. -/
theorem nativeK1K2Target_actual : nativeK1K2Target X := by
  intro p _ place u
  exact ABCBridge.LogKummerK1K2Consumer.logKummerK1K2_consumer place u

/-- Native archimedean target: existence of an actual selected infinite place
of the native source.  The archimedean log-shell data itself has no production
native type; the exact missing declaration is recorded below. -/
def nativeArchimedeanTarget : Prop :=
  Nonempty { v : NativePlaces X.S //
    NumberFieldPlace.IsInfinite
      (NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) v.1) }

/-! ## Exact missing production declarations

1. Native G_v action/action descent: production has only the conditional
   `SourceLogShellXMuChainActionCompatibility`; no native C1-indexed action
   constructed from `N8NativeInput` exists.  The target above states the exact
   conditional type with the native family and actual permutation group.
2. Native Kummer/root-change map: production has only
   `SourceLogShellDatum.codomainKummerContained : Prop` and conditional
   `SourceLogShellXMuChainSupply`; no actual native root-change map type exists.
3. Native multi-place K1/K2: production provides the actual per-completion
   `LogKummerK1K2.principalUnitMap` and its square; the target quantifies it over
   all finite places and is proved here (actual constructor).  No extra native
   multi-place boundary type is needed for this slice.
4. Native archimedean: production has no actual native archimedean source type;
   only conditional archimedean reduction predicates exist elsewhere.
-/

end LeanFormal.IUT.N8Closure.C2Targets
