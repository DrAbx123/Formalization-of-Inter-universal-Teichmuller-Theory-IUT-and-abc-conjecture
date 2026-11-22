import tmp.sheaf.xif.paper.TensorUnconditionalActual
import tmp.sheaf.n8.closure.C3OverFTensorTarget
import tmp.sheaf.n8.closure.C3TensorConstruction
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion

/-!
# Conditional Fmod tensor landing from the over-F tensor data

The actual over-F tensor carrier/landing is constructed in
TensorUnconditionalActual. The frozen Fmod tensor target uses Fmod-completion
factors, while the native q lives in the F-completion.

This file constructs:

* the actual Fmod base place and its common-prime tensor block type;
* an Fmod one-factor tensor carrier type;
* a conditional Fmod tensor landing and tensor unit from an explicit
  F-completion -> Fmod-completion map;
* the exact missing map object FCompletionToFmodCompletionMap.

The map is not constructed, chosen, or inferred from countability. It is the
exact missing source comparison. No arbitrary map, toy carrier, inequality,
axiom, or sorry is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Closure
namespace FmodTensorLandingActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open ABCBridge.N8.C3TensorTargetCorrection
open ABCBridge.N8.C3OverFTensorTarget
open LeanFormal.IUT.N8Closure.TensorUnconditionalActual

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual Fmod base place under the native bad moduli place. -/
abbrev nativeFmodBasePlace : NumberField.FinitePlace X.S.arithmetic.Fmod :=
  nativeBadBasePlace X

/-- The rational prime under the Fmod base place. -/
noncomputable def nativePrimeFmod : Nat :=
  (completionRationalPrime (nativeFmodBasePlace X)).val

instance nativePrimeFmodFact : Fact (Nat.Prime (nativePrimeFmod X)) :=
  ⟨(completionRationalPrime (nativeFmodBasePlace X)).2⟩

/-- The actual Fmod base place as a FinitePlaceAtPrime. -/
noncomputable def nativeFmodPlaceAtPrime :
    FinitePlaceAtPrime X.S.arithmetic.Fmod (nativePrimeFmod X) :=
  ⟨nativeFmodBasePlace X, rfl⟩

/-- The actual one-factor Fmod tensor carrier at the native base place. -/
abbrev nativeFmodTensorCarrier : Type :=
  FinitePadicTensor (p := nativePrimeFmod X)
    (fun _ : PUnit => CommonPrimeCompletion (nativeFmodPlaceAtPrime X))

/-- Exact missing source comparison: an F-completion -> Fmod-completion map at
the native base place. This is the only object needed by the conditional
Fmod tensor landing below. -/
structure FCompletionToFmodCompletionMap where
  toFmod : Completion (nativeFPlaceOverBad X) →
    CommonPrimeCompletion (nativeFmodPlaceAtPrime X)

/-- Conditional Fmod tensor landing: insert the mapped F-completion element into
the one-factor Fmod tensor carrier. -/
noncomputable def fmodTensorLanding
    (M : FCompletionToFmodCompletionMap (X := X)) :
    Completion (nativeFPlaceOverBad X) → nativeFmodTensorCarrier (X := X) :=
  fun z =>
    finitePadicTensorTprod (p := nativePrimeFmod X)
      (M := fun _ : PUnit =>
        CommonPrimeCompletion (nativeFmodPlaceAtPrime X))
      (fun _ => M.toFmod z)

/-- Conditional Fmod tensor unit: the landing of the actual native q-unit. -/
noncomputable def fmodTensorUnit
    (M : FCompletionToFmodCompletionMap (X := X)) :
    nativeFmodTensorCarrier (X := X) :=
  fmodTensorLanding X M (nativeQUnitActual X)

/-- The actual q lands at the conditional Fmod tensor unit. -/
theorem fmodTensorLanding_q
    (M : FCompletionToFmodCompletionMap (X := X)) :
    fmodTensorLanding X M (nativeQUnitActual X) = fmodTensorUnit X M :=
  rfl

/-- The conditional Fmod tensor landing data. -/
structure FmodTensorLandingData where
  map : FCompletionToFmodCompletionMap (X := X)
  tensorLanding : Completion (nativeFPlaceOverBad X) → nativeFmodTensorCarrier (X := X)
  tensorUnit : nativeFmodTensorCarrier (X := X)
  tensorLanding_q : tensorLanding (nativeQUnitActual X) = tensorUnit

/-- Actual Fmod tensor landing data from the explicit missing map. -/
noncomputable def fmodTensorLandingData
    (M : FCompletionToFmodCompletionMap (X := X)) :
    FmodTensorLandingData X where
  map := M
  tensorLanding := fmodTensorLanding X M
  tensorUnit := fmodTensorUnit X M
  tensorLanding_q := fmodTensorLanding_q X M

/-- Exact missing map object: an actual F-completion -> Fmod-completion map at
the native base place. -/
def MissingFToFmodCompletionMap : Prop :=
  Nonempty (FCompletionToFmodCompletionMap (X := X))

/-- Conditional actual Fmod tensor landing from the exact missing map. -/
theorem fmodTensorLandingData_nonempty_of_map
    (M : FCompletionToFmodCompletionMap (X := X)) :
    Nonempty (FmodTensorLandingData X) :=
  ⟨fmodTensorLandingData X M⟩

/-- The frozen Fmod tensor target additionally requires the uniform q condition
over all NativeQDonor q's; the conditional one-factor landing only handles the
actual native q-unit. -/
def FrozenUniformQLandingRequired {l : PrimeGeFive} (X : N8NativeInput l) : Prop :=
  FrozenTensorLandingRequired.{v, w} X

end FmodTensorLandingActual
end LeanFormal.IUT.N8Closure
end
