import tmp.sheaf.n8.closure.NativeC3

/-! # CONDITIONAL STATUS (xi-f)

Conditional on NativeTensorCarrierSource and NativeTensorLandingMapData. No production F -> Fmod tensor landing exists.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# Native tensor landing: conditional construction and exact missing map

The frozen target is NativeTensorLandingDonor of NativeC3.lean.  Its data are

* p, tensorIndex/PlaceIndex/Places/Tuple, and a tensorUnit in the arithmetic
  tensor block over the Fmod-prime places;
* tensorLanding : Completion (nativeFPlaceOverBad X) -> ArithmeticTensorTupleBlock;
* tensorLanding_q : for every NativeQDonor D, the landing at nativeQ X D.q is the
  tensorUnit.

The tree contains the actual native q/roots/Kummer data, but it does not contain
a production map from the F-completion to an Fmod arithmetic tensor block.  In
particular the only completion map available is the restriction map
Fmod-completion -> F-completion, not the reverse; see NativeC3.lean:16-18 and
C3TensorConstruction.lean:19-34.  The tensor index/places/tuple/unit are also
not projected from SourceNativeInitialThetaData.

This file therefore gives the exact conditional construction from the missing
carrier/landing data and states the missing map as a concrete structure.  No
arbitrary map, PUnit, True, axiom, or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.N8Closure.TensorLandingActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-! ## 1. The missing tensor carrier -/

/-- Exact missing carrier fields for the native tensor block.  This is data
projected from a hypothetical actual source tensor construction, not a toy
index or unit. -/
structure NativeTensorCarrierSource where
  p : Nat
  [hp : Fact p.Prime]
  tensorIndex : Type v
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex -> Type w
  tensorPlaces : (i : tensorIndex) -> tensorPlaceIndex i ->
    FinitePlaceAtPrime X.S.arithmetic.Fmod p
  tensorTuple : (i : tensorIndex) -> tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ

attribute [instance] NativeTensorCarrierSource.hp
attribute [instance] NativeTensorCarrierSource.tensorFintype

/-- Exact missing tensor landing map, including its uniform q-landing law. -/
structure NativeTensorLandingMapData
    (C : NativeTensorCarrierSource.{v, w} (X := X)) where
  landing : Completion (nativeFPlaceOverBad X) ->
    ArithmeticTensorTupleBlock C.tensorPlaces C.tensorTuple
  landing_q : forall (D : NativeQDonor X),
    landing (nativeQ X D).q =
      (C.tensorUnit : ArithmeticTensorTupleBlock C.tensorPlaces C.tensorTuple)

/-- The exact missing primitive: existence of the completion-to-tensor landing
map with the uniform q-landing property. -/
def MissingNativeTensorLandingMap
    (C : NativeTensorCarrierSource.{v, w} (X := X)) : Prop :=
  Nonempty (NativeTensorLandingMapData.{v, w} (X := X) C)

/-- Carrier plus landing: the exact data of NativeTensorLandingDonor. -/
structure NativeTensorLandingSource where
  carrier : NativeTensorCarrierSource.{v, w} (X := X)
  landing : Completion (nativeFPlaceOverBad X) ->
    ArithmeticTensorTupleBlock carrier.tensorPlaces carrier.tensorTuple
  landing_q : forall (D : NativeQDonor X),
    landing (nativeQ X D).q =
      (carrier.tensorUnit :
        ArithmeticTensorTupleBlock carrier.tensorPlaces carrier.tensorTuple)

/-! ## 2. Actual conditional constructor -/

/-- The conditional actual construction of NativeTensorLandingDonor. -/
noncomputable def nativeTensorLandingDonorOfSource
    (S : NativeTensorLandingSource.{v, w} (X := X)) :
    NativeTensorLandingDonor.{v, w} X where
  p := S.carrier.p
  hp := S.carrier.hp
  tensorIndex := S.carrier.tensorIndex
  tensorFintype := S.carrier.tensorFintype
  tensorPlaceIndex := S.carrier.tensorPlaceIndex
  tensorPlaces := S.carrier.tensorPlaces
  tensorTuple := S.carrier.tensorTuple
  tensorUnit := S.carrier.tensorUnit
  tensorLanding := S.landing
  tensorLanding_q := S.landing_q

/-- The constructed donor has exactly the supplied carrier and landing. -/
@[simp] theorem nativeTensorLandingDonorOfSource_tensorLanding
    (S : NativeTensorLandingSource.{v, w} (X := X)) :
    (nativeTensorLandingDonorOfSource (X := X) S).tensorLanding = S.landing :=
  rfl

/-- The q-landing field of the constructed donor is the supplied uniform law. -/
theorem nativeTensorLandingDonorOfSource_tensorLanding_q
    (S : NativeTensorLandingSource.{v, w} (X := X)) (D : NativeQDonor X) :
    (nativeTensorLandingDonorOfSource (X := X) S).tensorLanding
        (nativeQ X D).q =
      ((nativeTensorLandingDonorOfSource (X := X) S).tensorUnit :
        ArithmeticTensorTupleBlock
          (nativeTensorLandingDonorOfSource (X := X) S).tensorPlaces
          (nativeTensorLandingDonorOfSource (X := X) S).tensorTuple) :=
  S.landing_q D

/-- The conditional donor exists once the carrier and landing map exist. -/
theorem nativeTensorLandingDonorOfCarrierAndMap
    (C : NativeTensorCarrierSource.{v, w} (X := X))
    (M : NativeTensorLandingMapData.{v, w} (X := X) C) :
    Nonempty (NativeTensorLandingDonor.{v, w} X) :=
  ⟨nativeTensorLandingDonorOfSource (X := X)
    { carrier := C, landing := M.landing, landing_q := M.landing_q}⟩

/-! ## 3. Exact missing object -/

/-- The exact missing source object is a carrier plus the F-completion ->
Fmod-tensor landing map.  This packages the two things the current native
source does not produce. -/
def NativeTensorLandingMissing
    (C : NativeTensorCarrierSource.{v, w} (X := X)) : Prop :=
  MissingNativeTensorLandingMap (X := X) C

/-- If the exact missing map is supplied for an actual carrier, the frozen donor
follows. -/
theorem nativeTensorLandingDonorOfMissingMap
    (C : NativeTensorCarrierSource.{v, w} (X := X))
    (h : NativeTensorLandingMissing (X := X) C) :
    Nonempty (NativeTensorLandingDonor.{v, w} X) := by
  rcases h with ⟨M⟩
  exact nativeTensorLandingDonorOfCarrierAndMap (X := X) C M

end LeanFormal.IUT.N8Closure.TensorLandingActual

end