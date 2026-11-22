import tmp.sheaf.xif.paper.TensorLandingActual

/-! # CONDITIONAL STATUS (xi-f)

Conditional on SourceTensorLandingData: source tensor carrier fields and F-completion -> Fmod tensor block landing are explicit missing data.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# Tensor carrier and landing from source data: deeper attempt

This file refines the conditional layer of TensorLandingActual by separating
the two missing source objects.

The frozen NativeTensorLandingDonor of NativeC3 requires:

* a tensor carrier: p, tensorIndex, tensorPlaceIndex, tensorPlaces over the
  Fmod-prime places, tensorTuple, and a tensorUnit;
* a landing map Completion (nativeFPlaceOverBad X) -> ArithmeticTensorTupleBlock;
* the uniform q-landing law for every NativeQDonor.

What the actual source tree supplies is the native F-place, the actual q/roots/
Kummer data, and the canonical number-field prime strip.  It does not supply a
tensor index/places/tuple/unit for the q-pilot tensor block, and it does not
supply an F-completion -> Fmod-tensor landing map.  The only completion map in
the tree is the restriction Fmod-completion -> F-completion, in the opposite
direction (NativeC3.lean:16-18, C3TensorConstruction.lean:19-34).

This file therefore gives exact source-data structures and the zero-sorry
conditional construction from them.  No arbitrary map, PUnit, True, axiom, or
sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.N8Closure.TensorLandingFromSource

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.TensorLandingActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-! ## 1. Exact source tensor carrier data -/

/-- The actual source fields needed to form the tensor carrier.  This is data,
not an arbitrary choice: every field is a supplied source tensor object. -/
structure SourceTensorCarrierData where
  p : Nat
  [hp : Fact p.Prime]
  tensorIndex : Type v
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex -> Type w
  tensorPlaces : (i : tensorIndex) -> tensorPlaceIndex i ->
    FinitePlaceAtPrime X.S.arithmetic.Fmod p
  tensorTuple : (i : tensorIndex) -> tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ

attribute [instance] SourceTensorCarrierData.hp
attribute [instance] SourceTensorCarrierData.tensorFintype

/-- The source carrier data gives the exact carrier of TensorLandingActual. -/
noncomputable def carrierOfSource
    (C : SourceTensorCarrierData.{v, w} (X := X)) :
    NativeTensorCarrierSource.{v, w} (X := X) where
  p := C.p
  hp := C.hp
  tensorIndex := C.tensorIndex
  tensorFintype := C.tensorFintype
  tensorPlaceIndex := C.tensorPlaceIndex
  tensorPlaces := C.tensorPlaces
  tensorTuple := C.tensorTuple
  tensorUnit := C.tensorUnit

/-- The exact missing carrier: no source projection produces these fields. -/
def MissingSourceTensorCarrier : Prop :=
  Nonempty (SourceTensorCarrierData.{v, w} (X := X))

/-! ## 2. Exact source landing data -/

/-- The exact missing landing map for a supplied source carrier. -/
structure SourceTensorLandingData
    (C : SourceTensorCarrierData.{v, w} (X := X)) where
  landing : Completion (nativeFPlaceOverBad X) ->
    ArithmeticTensorTupleBlock C.tensorPlaces C.tensorTuple
  landing_q : forall (D : NativeQDonor X),
    landing (nativeQ X D).q =
      (C.tensorUnit : ArithmeticTensorTupleBlock C.tensorPlaces C.tensorTuple)

/-- A supplied source landing map is exactly the map data of the conditional
layer. -/
noncomputable def landingMapDataOfSource
    (C : SourceTensorCarrierData.{v, w} (X := X))
    (L : SourceTensorLandingData.{v, w} (X := X) C) :
    NativeTensorLandingMapData.{v, w} (X := X) (carrierOfSource (X := X) C) where
  landing := L.landing
  landing_q := L.landing_q

/-- The exact missing landing map: no production F-completion -> Fmod-tensor
map exists. -/
def MissingSourceTensorLanding
    (C : SourceTensorCarrierData.{v, w} (X := X)) : Prop :=
  Nonempty (SourceTensorLandingData.{v, w} (X := X) C)

/-! ## 3. Conditional donor and exact missing object -/

/-- Carrier plus source landing data gives the exact frozen donor. -/
noncomputable def nativeTensorLandingDonorOfSourceData
    (C : SourceTensorCarrierData.{v, w} (X := X))
    (L : SourceTensorLandingData.{v, w} (X := X) C) :
    NativeTensorLandingDonor.{v, w} X :=
  nativeTensorLandingDonorOfSource (X := X)
    { carrier := carrierOfSource (X := X) C
      landing := L.landing
      landing_q := L.landing_q }

/-- The conditional donor exists as soon as the exact carrier and landing data
are supplied. -/
theorem nativeTensorLandingDonorOfSourceData_nonempty
    (C : SourceTensorCarrierData.{v, w} (X := X))
    (L : SourceTensorLandingData.{v, w} (X := X) C) :
    Nonempty (NativeTensorLandingDonor.{v, w} X) :=
  ⟨nativeTensorLandingDonorOfSourceData (X := X) C L⟩

/-- The exact combined missing object: source carrier data plus source landing
data.  This is the precise primitive absent from the tree. -/
structure NativeTensorLandingSourceData where
  carrier : SourceTensorCarrierData.{v, w} (X := X)
  landing : SourceTensorLandingData.{v, w} (X := X) carrier

/-- The combined source data gives the actual donor. -/
noncomputable def nativeTensorLandingDonorOfCombined
    (S : NativeTensorLandingSourceData.{v, w} (X := X)) :
    NativeTensorLandingDonor.{v, w} X :=
  nativeTensorLandingDonorOfSourceData (X := X) S.carrier S.landing

/-- The frozen donor is constructible exactly from the combined source data. -/
theorem nativeTensorLandingDonor_of_combined_nonempty
    (S : NativeTensorLandingSourceData.{v, w} (X := X)) :
    Nonempty (NativeTensorLandingDonor.{v, w} X) :=
  ⟨nativeTensorLandingDonorOfCombined (X := X) S⟩

/-- Exact unresolved primitive: an inhabitant of the combined source data. -/
def MissingNativeTensorLandingSourceData : Prop :=
  Nonempty (NativeTensorLandingSourceData.{v, w} (X := X))

end LeanFormal.IUT.N8Closure.TensorLandingFromSource

end