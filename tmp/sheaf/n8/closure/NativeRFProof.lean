import tmp.sheaf.n8.closure.NativeBindingRFActual
import tmp.sheaf.n8.closure.C1FiberMonEquivAttempt
import tmp.sheaf.n8.closure.C1FiberMonTargetNoGo
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull

/-!
# Native R/F proof attempt: SourceImageRealization and fiberMonEquiv at badPlace

This is a write-only deep attempt.  It reuses the exact field packages from
NativeBindingRFActual and tries to construct their two contents from the actual
native theta/value-monoid/prime-strip data.

What is constructible here:

1. Every hypothetical native SourceImageRealization at badPlace X is exactly a
   pair (posRealAction, degree_of_q); the file packages the conversion in both
   directions.
2. A genuine partial image realization exists when the native theta packet has
   q = 1: the constant unit monoid hom has degree zero, so it satisfies the q
   faithfulness equation.  This is an actual construction at the native
   selected place, not V = Unit data.
3. The full fiber field is exactly a family of monoid equivalences from the old
   strip fibers to SourcePlaceValueGroup; no production inhabitant exists.

What is missing:

* nativePosRealAction : Multiplicative Real ->* I.ValueMonoidAt 0 0 (badPlace X)
  with its q-degree equation, for native q != 1;
* nativeFiberMonEquiv : forall n m v, (I.primeStripAt n m).Mon v =*=
  SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (e v).

The only production positive-real action is sourceHaarActualPositiveRealAction
in SourceUnitRegionHaarDataActual.lean (V = Unit, q = 1), whose file is red.
NativeC1.NativeStripFiberComparison (NativeC1.lean:186) is still an uninhabited
named obligation.  The C1FiberMonTargetNoGo file shows that the raw local unit
monoid is not equivalent to the value group; the correct fiber target requires
the actual quotient map, which is not a native prime-strip identification.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeRFProof

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeBindingRFActual
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)
variable (I : OriginalInput l (NativePlaces X.S))

/-! ## 1. The selected native place and the image-field direction -/

/-- Reused actual native selected place. -/
abbrev nativeSelectedPlace : NativePlaces X.S :=
  NativeBindingRFActual.nativeSelectedPlace X

/-- A hypothetical SourceImageRealization at the native selected place gives
exactly the two source fields. -/
def imageFieldsOfRealization
    (R : I.SourceImageRealization (nativeSelectedPlace X)) :
    NativeImageRealizationSourceFields X I where
  posRealAction := R.posRealAction
  degree_of_q := R.degree_of_q

/-- Conversely, the two exact source fields construct the realization. -/
def realizationOfImageFields
    (R : NativeImageRealizationSourceFields X I) :
    I.SourceImageRealization (nativeSelectedPlace X) :=
  NativeBindingRFActual.nativeImageRealizationOfFields X I R

/-- The image-field package is exactly the missing realization at badPlace X. -/
theorem imageFields_nonempty_iff :
    Nonempty (NativeImageRealizationSourceFields X I) ↔
      Nonempty (I.SourceImageRealization (nativeSelectedPlace X)) := by
  constructor
  · rintro ⟨R⟩
    exact ⟨realizationOfImageFields (X := X) I R⟩
  · rintro ⟨R⟩
    exact ⟨imageFieldsOfRealization (X := X) I R⟩

/-! ## 2. A genuine partial image realization at native q = 1 -/

/-- The constant unit hom from the positive reals into any value monoid. -/
def trivialPositiveRealAction (v : NativePlaces X.S) :
    Multiplicative Real →* I.ValueMonoidAt 0 0 v :=
  1

/-- The trivial positive-real action has zero degree. -/
theorem logDegreeAt_trivialPositiveRealAction
    (v : NativePlaces X.S) (x : Multiplicative Real) :
    I.logDegreeAt 0 0 v (trivialPositiveRealAction (X := X) I v x) = 0 := by
  change I.logDegreeAt 0 0 v (1 : I.ValueMonoidAt 0 0 v) = 0
  exact I.logDegreeAt_one 0 0 v

/-- Actual partial construction: if the native theta packet at the selected
place has q = 1, the constant unit action satisfies the q-degree faithfulness
equation, giving a real SourceImageRealization at badPlace X. -/
def realizationOfImageFieldsAtQOne
    (hq : (I.theaterAt 0 0).thetaPacket.q = 1) :
    I.SourceImageRealization (nativeSelectedPlace X) where
  posRealAction := trivialPositiveRealAction (X := X) I (nativeSelectedPlace X)
  degree_of_q := by
    simp [trivialPositiveRealAction, hq, I.logDegreeAt_one]

theorem sourceImageRealization_nonempty_of_q_one
    (hq : (I.theaterAt 0 0).thetaPacket.q = 1) :
    Nonempty (I.SourceImageRealization (nativeSelectedPlace X)) :=
  ⟨realizationOfImageFieldsAtQOne (X := X) I hq⟩

/-! ## 3. The fiber-field direction -/

/-- A hypothetical native fiber equivalence gives exactly the existing fiber
source-field package. -/
def fiberFieldsOfEquiv
    (e : NativePlaces X.S ≃
      NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (F : ∀ (n m : Int) (v : NativePlaces X.S),
      (I.primeStripAt n m).Mon v ≃*
        SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (e v)) :
    NativeFiberSourceFields X I e where
  fiberMonEquiv := F

/-- Conversely, the source-field package is exactly the required fiber map. -/
def fiberEquivOfFields
    {e : NativePlaces X.S ≃
      NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)}
    (F : NativeFiberSourceFields X I e) :
    ∀ (n m : Int) (v : NativePlaces X.S),
      (I.primeStripAt n m).Mon v ≃*
        SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (e v) :=
  NativeBindingRFActual.nativeFiberEquivOfFields X I F

theorem fiberFields_nonempty_iff
    (e : NativePlaces X.S ≃
      NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)) :
    Nonempty (NativeFiberSourceFields X I e) ↔
      Nonempty (∀ (n m : Int) (v : NativePlaces X.S),
        (I.primeStripAt n m).Mon v ≃*
          SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (e v)) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨fiberEquivOfFields (X := X) I F⟩
  · rintro ⟨F⟩
    exact ⟨fiberFieldsOfEquiv (X := X) I e F⟩

/-! ## 4. The exact remaining primitive -/

/-- The two missing native source primitives, packaged exactly.  This is a
statement of what the deep attempt could not produce, not a surrogate. -/
structure NativeRFMissingPrimitive where
  /-- The explicit native place-index equivalence. -/
  placeEquiv : NativePlaces X.S ≃
    NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)
  /-- The missing native positive-real action at badPlace X. -/
  posRealAction : Multiplicative Real →* I.ValueMonoidAt 0 0 (nativeSelectedPlace X)
  /-- The missing q-degree faithfulness equation for that action. -/
  degree_of_q : I.logDegreeAt 0 0 (nativeSelectedPlace X)
      (posRealAction (Multiplicative.ofAdd
        (Real.log ((I.theaterAt 0 0).thetaPacket.q)))) =
    Real.log ((I.theaterAt 0 0).thetaPacket.q)
  /-- The missing native strip-fiber equivalence. -/
  fiberMonEquiv : ∀ (n m : Int) (v : NativePlaces X.S),
    (I.primeStripAt n m).Mon v ≃*
      SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (placeEquiv v)

/-- The exact missing primitive is equivalent to the image field together with
the fiber field at the selected place. -/
def missingPrimitiveToFields
    (P : NativeRFMissingPrimitive (X := X) I) :
    NativeImageRealizationSourceFields X I :=
  { posRealAction := P.posRealAction
    degree_of_q := P.degree_of_q }

/-- The fiber component of the missing primitive.  The place indexing is fixed
to the native selected place; this is the exact map required by the old C1
binding at that place. -/
def missingPrimitiveFiber
    (P : NativeRFMissingPrimitive (X := X) I) :
    ∀ (n m : Int) (v : NativePlaces X.S),
      (I.primeStripAt n m).Mon v ≃*
        SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (P.placeEquiv v) :=
  P.fiberMonEquiv

/-- The realized native binding would follow from the missing primitive once the
indexing equivalence e is supplied. -/
def nativeBindingOfMissingPrimitive
    (P : NativeRFMissingPrimitive (X := X) I) :
    NativePlaceBindingDonors X I :=
  { placeEquiv := P.placeEquiv
    selected := nativeSelectedPlace X
    selected_realization :=
      NativeBindingRFActual.nativeImageRealizationOfFields X I
        (missingPrimitiveToFields (X := X) I P)
    fiberMonEquiv := P.fiberMonEquiv }

end LeanFormal.IUT.N8Closure.NativeRFProof

end