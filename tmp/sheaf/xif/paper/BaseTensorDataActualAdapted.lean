import tmp.sheaf.xif.paper.TensorUnconditionalActual
import tmp.sheaf.xif.paper.C3DonorUnconditionalActual
import tmp.sheaf.xif.paper.BasePlaceQCandidateActual

/-! # BaseTensorData from native tensor data: actual object and exact missing

Task-630.  The native actual tensor construction of
`TensorUnconditionalActual` supplies an over-F carrier and landing:

* `nativeTensorCarrier : overFC3TensorBlock X`;
* `nativeTensorLanding : Completion (nativeFPlaceOverBad X) -> carrier`;
* `nativeTensorUnit = nativeTensorLanding (nativeQUnitActual X)`;
* `nativeTensorLanding_q` is `rfl`.

`BaseTensorData` (C3DonorUnconditionalActual) instead requires

* tensor places in `FinitePlaceAtPrime X.S.arithmetic.Fmod`;
* a landing from `CommonPrimeCompletion (K := X.S.arithmetic.Fmod)
  (nativeC3Place X)` to the arithmetic tensor block;
* the base q landing equality with `tensorUnit`.

The native carrier is over `X.S.arithmetic.F`, not `Fmod`; the native q lives
in the F-completion, while the base q lives in the Fmod-completion.  The tree
has no Fmod-indexed tensor carrier, no F-to-Fmod completion landing, and no
base `tensorLanding_q`.  Therefore the native over-F object cannot be used as
`BaseTensorData`.

## Constructed actual over-F object

`nativeTensorCarrierSource` and its projections are actual declarations from
`TensorUnconditionalActual`; no new arbitrary carrier is introduced.

## Exact missing base object

`MissingBaseTensorLanding` records exactly: Fmod-indexed tensorIndex/
tensorPlaceIndex/tensorPlaces/tensorTuple, a `tensorUnit`, a base-completion
`tensorLanding`, and the `tensorLanding_q` equality.  No inhabitant is
asserted.  No PUnit toy, arbitrary map, axiom, or sorry is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.BaseTensorDataActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.TensorUnconditionalActual
open LeanFormal.IUT.N8Closure.C3DonorUnconditionalActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {V : Type uv} (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Actual over-F native tensor carrier supplied by the native construction. -/
abbrev ActualNativeTensorCarrier : Type :=
  NativeTensorCarrierType (X := X)

/-- Actual over-F tensor landing. -/
def actualNativeTensorLanding :
    Completion (nativeFPlaceOverBad X) -> ActualNativeTensorCarrier (X := X) :=
  nativeTensorLanding X

/-- Actual over-F tensor unit. -/
def actualNativeTensorUnit : ActualNativeTensorCarrier (X := X) :=
  nativeTensorUnit X

/-- Actual over-F landing at the native q unit. -/
theorem actualNativeTensorLanding_q :
    actualNativeTensorLanding X (nativeQUnitActual X) =
      actualNativeTensorUnit X :=
  nativeTensorLanding_q X

/-- The actual native tensor source object. -/
abbrev actualNativeTensorSource : NativeTensorCarrierSource X :=
  nativeTensorCarrierSource X

/-- The exact missing base tensor data: Fmod-indexed carrier and base landing.
This is the same field surface as `BaseTensorData`, kept as an explicit
obligation because the native construction is over F. -/
structure MissingBaseTensorLanding where
  tensorIndex : Type (max ua uv)
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex -> Type
  tensorPlaces : (i : tensorIndex) -> tensorPlaceIndex i ->
    FinitePlaceAtPrime X.S.arithmetic.Fmod (nativeC3Prime X)
  tensorTuple : (i : tensorIndex) -> tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ
  tensorLanding :
    CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X) ->
      ArithmeticTensorTupleBlock tensorPlaces tensorTuple
  tensorLanding_q : tensorLanding
      ((baseQCandidateOfDescent (X := X)).q :
        CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X)) =
    (tensorUnit : ArithmeticTensorTupleBlock tensorPlaces tensorTuple)

/-- A base tensor landing + carrier data yields exactly `BaseTensorData`. -/
def baseTensorDataOfMissing
    (M : MissingBaseTensorLanding (X := X)) :
    BaseTensorData (X := X) (baseQCandidateOfDescent (X := X)) where
  tensorIndex := M.tensorIndex
  tensorFintype := M.tensorFintype
  tensorPlaceIndex := M.tensorPlaceIndex
  tensorPlaces := M.tensorPlaces
  tensorTuple := M.tensorTuple
  tensorUnit := M.tensorUnit
  tensorLanding := M.tensorLanding
  tensorLanding_q := M.tensorLanding_q

/-- Exact missing proposition for the base tensor object. -/
def BaseTensorDataRequired : Prop :=
  Nonempty (MissingBaseTensorLanding (X := X))

/-- The native over-F tensor is actual, but it is not the base Fmod tensor. -/
theorem nativeTensor_not_baseTensor :
    ActualNativeTensorCarrier (X := X) = OverFC3TensorBlock X := rfl

end LeanFormal.IUT.XiFPaper.BaseTensorDataActualAdapted

end
