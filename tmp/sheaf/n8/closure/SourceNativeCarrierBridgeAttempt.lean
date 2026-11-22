import tmp.sheaf.n8.closure.P6SourceVolumeCarrierMapAttempt
import tmp.sheaf.n8.closure.N8NativeClosure
import tmp.sheaf.n8.closure.NativeC1

/-!
# Attempt: construct SourceNativeCarrierBridge from C1

The target is P6SourceVolumeCarrierMapAttempt.SourceNativeCarrierBridge:
  placeEquiv : V ≃ NativePlaces X.S
  monoidEquiv : forall w, (I.primeStripAt 0 0).Mon (placeEquiv.symm w) ≃* localFieldAt X w

C1 supplies:
- NativeOldC1Bridge X with input over OriginalInput l (NativePlaces X.S);
- binding.place.placeEquiv : NativePlaces X.S ≃ NumberFieldPlaceIndex;
- binding.place.fiberMonEquiv :
    (I.primeStripAt n m).Mon v ≃* SourcePlaceValueGroup F (placeEquiv v).

Thus an actual place equivalence NativePlaces ≃ NativePlaces is obtainable by
composing the C1 place equivalence with the native index equivalence.  The
monoid target of C1 fiberMonEquiv is SourcePlaceValueGroup (a multiplicative
integer/real value group), not localFieldAt X w (the native local field).
No production equivalence SourcePlaceValueGroup ≃* localFieldAt exists.

For arbitrary V the C1 bridge input is fixed to NativePlaces, so no
V ≃ NativePlaces and no monoid equivalence are available.  No arbitrary
equivalence is introduced; the remaining monoid bridge is named.
This file does not edit owner files.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.SourceNativeCarrierBridgeAttempt

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeClosure
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

variable {l : PrimeGeFive}

/-- Actual C1-derived place equivalence for the native-place input.  The old
C1 placeEquiv goes to NumberFieldPlaceIndex; composing with the native index
equivalence returns NativePlaces. -/
noncomputable def sourceNativePlaceEquivOfBridge
    (X : N8NativeInput l) (B : NativeOldC1Bridge X)
    (harith : B.input.initial.arithmetic = X.S.arithmetic) :
    NativePlaces X.S ≃ NativePlaces X.S :=
  B.binding.place.placeEquiv.trans
    (harith.symm ▸ (nativePlaceIndexEquiv X)).symm

/-- Evaluation of the actual C1-derived place equivalence. -/
theorem sourceNativePlaceEquivOfBridge_apply
    (X : N8NativeInput l) (B : NativeOldC1Bridge X)
    (harith : B.input.initial.arithmetic = X.S.arithmetic)
    (v : NativePlaces X.S) :
    sourceNativePlaceEquivOfBridge X B harith v =
      (harith.symm ▸ (nativePlaceIndexEquiv X)).symm
        (B.binding.place.placeEquiv v) :=
  rfl

/-- Exact missing monoid bridge: source prime-strip value monoid is the native
local field at the C1-derived place.  C1 fiberMonEquiv itself targets
SourcePlaceValueGroup, not localFieldAt. -/
def SourceNativeMonoidEquivTarget
    (X : N8NativeInput l) (B : NativeOldC1Bridge X)
    (harith : B.input.initial.arithmetic = X.S.arithmetic)
    [∀ w : NativePlaces X.S, NormedField (localFieldAt X w)] : Prop :=
  Nonempty (∀ w : NativePlaces X.S,
    (B.input.primeStripAt 0 0).Mon
        ((sourceNativePlaceEquivOfBridge X B harith).symm w) ≃* localFieldAt X w)

end LeanFormal.IUT.N8Closure.SourceNativeCarrierBridgeAttempt
