import tmp.sheaf.n8.closure.C3OverFTensorTarget
import tmp.sheaf.n8.closure.C3TensorConstruction
import tmp.sheaf.n8.closure.C3TensorTargetCorrection

/-! # CONDITIONAL STATUS (xi-f)

Constructs only the over-F tensor carrier/landing. The source-faithful F-completion -> Fmod tensor block landing (FrozenTensorLandingRequired) is missing.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# Actual native tensor carrier and landing over F

This file constructs the actual over-F native tensor carrier and landing from
the actual source/native data:

* the native F-place over the selected bad moduli place (NativeC3);
* the actual native Clause (b) q-unit (NativeC3.nativeQUnitActual);
* the canonical finite-p-adic tensor insertion over F
  (C3OverFTensorTarget.overFTensorLanding).

The resulting NativeTensorCarrierSource has actual tensor places in
FinitePlaceAtPrime F p, actual tensorTuple = PUnit, actual tensorUnit, and the
actual tensorLanding. Its tensorLanding_q is rfl.

The frozen Fmod tensor target NativeTensorLandingDonor is NOT constructed: the
q-unit lives in the F-completion, while the frozen tensor block uses Fmod
completion factors. The current tree has no source comparison from the
F-completion to the Fmod-completion tensor block. That exact missing object is
recorded as FrozenTensorLandingRequired.

No arbitrary map, toy carrier, inequality, axiom, or sorry is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Closure
namespace TensorUnconditionalActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open ABCBridge.N8.C3TensorTargetCorrection
open ABCBridge.N8.C3OverFTensorTarget

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual over-F native tensor carrier: one F-completion factor at the
native F-place over the selected bad moduli place. -/
abbrev NativeTensorCarrierType {l : PrimeGeFive} (X : N8NativeInput l) : Type :=
  overFC3TensorBlock X

/-- The actual over-F tensor carrier. -/
abbrev nativeTensorCarrier {l : PrimeGeFive} (X : N8NativeInput l) : Type :=
  overFC3TensorBlock X

/-- The actual tensor carrier from the source/native data. -/
theorem nativeTensorCarrier_eq {l : PrimeGeFive} (X : N8NativeInput l) :
    nativeTensorCarrier X = overFC3TensorBlock X := rfl

/-- The actual over-F tensor landing, built by the canonical finite-p-adic
tensor insertion of the F-completion into the one-factor block. -/
noncomputable def nativeTensorLanding {l : PrimeGeFive} (X : N8NativeInput l) :
    Completion (nativeFPlaceOverBad X) → NativeTensorCarrierType X :=
  overFTensorLanding X

/-- The actual tensor unit is the landing of the actual native q-unit. -/
noncomputable def nativeTensorUnit {l : PrimeGeFive} (X : N8NativeInput l) :
    NativeTensorCarrierType X :=
  nativeTensorLanding X (nativeQUnitActual X)

/-- The actual q lands at the actual tensor unit. -/
theorem nativeTensorLanding_q {l : PrimeGeFive} (X : N8NativeInput l) :
    nativeTensorLanding X (nativeQUnitActual X) = nativeTensorUnit X := rfl

/-- The actual tensor places are the native F-place at prime p. -/
theorem nativeTensorLanding_places {l : PrimeGeFive} (X : N8NativeInput l) :
    fTensorPlaces X PUnit.unit PUnit.unit = nativeFPlaceAtPrime X := rfl

/-- The actual carrier/landing object. This is the over-F native tensor target,
not the frozen Fmod target. -/
structure NativeTensorCarrierSource where
  carrier : Type
  tensorUnit : carrier
  tensorLanding : Completion (nativeFPlaceOverBad X) → carrier
  tensorLanding_q : tensorLanding (nativeQUnitActual X) = tensorUnit

/-- Actual NativeTensorCarrierSource from the native q and the canonical
over-F tensor insertion. -/
noncomputable def nativeTensorCarrierSource {l : PrimeGeFive} (X : N8NativeInput l) :
    NativeTensorCarrierSource X where
  carrier := NativeTensorCarrierType X
  tensorUnit := nativeTensorUnit X
  tensorLanding := nativeTensorLanding X
  tensorLanding_q := nativeTensorLanding_q X

/-- Exact missing frozen target: an actual F-completion-to-Fmod-completion
tensor landing with the uniform q condition. This is the frozen
NativeTensorLandingDonor, which is not constructed here. -/
def FrozenTensorLandingRequired {l : PrimeGeFive} (X : N8NativeInput l) : Prop :=
  Nonempty (NativeTensorLandingDonor.{v, w} X)

/-- The over-F actual construction does not supply the frozen Fmod tensor
landing; the exact missing object is recorded as FrozenTensorLandingRequired. -/
def MissingFToFmodTensorLanding {l : PrimeGeFive} (X : N8NativeInput l) : Prop :=
  Nonempty (NativeTensorLandingDonor.{v, w} X)

/-- The actual over-F tensor data is inhabited unconditionally from the native
source data. -/
theorem nativeTensorCarrierSource_nonempty {l : PrimeGeFive} (X : N8NativeInput l) :
    Nonempty (NativeTensorCarrierSource X) :=
  ⟨nativeTensorCarrierSource X⟩

/-- The actual over-F landing is an actual function, not an existential
placeholder. -/
theorem nativeTensorLanding_apply {l : PrimeGeFive} (X : N8NativeInput l)
    (z : Completion (nativeFPlaceOverBad X)) :
    nativeTensorLanding X z =
      finitePadicTensorTprod (p := nativePrime X)
        (M := fun _ : PUnit => CommonPrimeCompletion (nativeFPlaceAtPrime X))
        (fun _ => cast (by rfl : Completion (nativeFPlaceOverBad X) =
          CommonPrimeCompletion (nativeFPlaceAtPrime X)) z) :=
  rfl

end TensorUnconditionalActual
end LeanFormal.IUT.N8Closure
end
