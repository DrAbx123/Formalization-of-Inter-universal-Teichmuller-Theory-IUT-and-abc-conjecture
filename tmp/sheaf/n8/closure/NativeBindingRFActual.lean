import tmp.sheaf.n8.closure.C10BridgeProof
import tmp.sheaf.n8.closure.NativeC1

/-!
# Conditional native binding: R and fiberMonEquiv at the native selected place

NativeC1 supplies the actual selected bad place badPlace X, but it does not
supply the two source objects required by NativePlaceBindingDonors:

* R : I.SourceImageRealization (badPlace X), whose exact fields are
  posRealAction : Multiplicative Real →* I.ValueMonoidAt 0 0 (badPlace X) and
  degree_of_q; and
* the prime-strip fiber equivalence
  forall n m v, (I.primeStripAt n m).Mon v ≃*
    SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (e v).

The only existing production realization is sourceHaarActualImageRealization
in SourceUnitRegionHaarDataActual.lean: it is for the synthetic V = Unit, q = 1
input and its file is red, so it cannot be used at the native selected place.
NativeC1.NativeStripFiberComparison is a named obligation with no inhabitant.
This file therefore gives the exact conditional construction and records the
missing source fields; it does not invent a realization or an equivalence.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeBindingRFActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)
variable (I : OriginalInput l (NativePlaces X.S))

/-- The selected native place, reused from NativeC1. -/
noncomputable def nativeSelectedPlace : NativePlaces X.S :=
  badPlace X

/-- The two exact source fields of a SourceImageRealization at the native
selected place.  These are data fields, not an arbitrary function: the first
is the positive-real value action, the second is the q-degree faithfulness
equation. -/
structure NativeImageRealizationSourceFields where
  posRealAction : Multiplicative Real →* I.ValueMonoidAt 0 0 (nativeSelectedPlace X)
  degree_of_q : I.logDegreeAt 0 0 (nativeSelectedPlace X)
      (posRealAction (Multiplicative.ofAdd
        (Real.log ((I.theaterAt 0 0).thetaPacket.q)))) =
    Real.log ((I.theaterAt 0 0).thetaPacket.q)

/-- Build the actual SourceImageRealization at badPlace X from its exact
source fields. -/
def nativeImageRealizationOfFields
    (R : NativeImageRealizationSourceFields X I) :
    I.SourceImageRealization (nativeSelectedPlace X) where
  posRealAction := R.posRealAction
  degree_of_q := R.degree_of_q

/-- Exact missing source fields for the prime-strip fiber equivalence over the
native selected place and a native place indexing equivalence e. -/
structure NativeFiberSourceFields
    (e : NativePlaces X.S ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)) where
  fiberMonEquiv : forall (n m : Int) (v : NativePlaces X.S),
    (I.primeStripAt n m).Mon v ≃*
      SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (e v)

/-- The actual fiber equivalence carried by the exact source fields. -/
def nativeFiberEquivOfFields
    {e : NativePlaces X.S ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)}
    (F : NativeFiberSourceFields X I e) :
    forall (n m : Int) (v : NativePlaces X.S),
      (I.primeStripAt n m).Mon v ≃*
        SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (e v) :=
  F.fiberMonEquiv

/-- Conditional construction of the exact NativePlaceBindingDonors record at
the native selected place.  The place equivalence is explicit; the realization
and fiber are computed from the two exact source-field structures above. -/
def nativePlaceBindingDonorsOfSource
    (e : NativePlaces X.S ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (R : NativeImageRealizationSourceFields X I)
    (F : NativeFiberSourceFields X I e) :
    NativePlaceBindingDonors X I where
  placeEquiv := e
  selected := nativeSelectedPlace X
  selected_realization := nativeImageRealizationOfFields X I R
  fiberMonEquiv := F.fiberMonEquiv

@[simp] theorem nativePlaceBindingDonorsOfSource_placeEquiv
    (e : NativePlaces X.S ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (R : NativeImageRealizationSourceFields X I)
    (F : NativeFiberSourceFields X I e) :
    (nativePlaceBindingDonorsOfSource X I e R F).placeEquiv = e :=
  rfl

@[simp] theorem nativePlaceBindingDonorsOfSource_selected
    (e : NativePlaces X.S ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (R : NativeImageRealizationSourceFields X I)
    (F : NativeFiberSourceFields X I e) :
    (nativePlaceBindingDonorsOfSource X I e R F).selected =
      badPlace X :=
  rfl

@[simp] theorem nativePlaceBindingDonorsOfSource_selected_realization
    (e : NativePlaces X.S ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (R : NativeImageRealizationSourceFields X I)
    (F : NativeFiberSourceFields X I e) :
    (nativePlaceBindingDonorsOfSource X I e R F).selected_realization =
      nativeImageRealizationOfFields X I R :=
  rfl

@[simp] theorem nativePlaceBindingDonorsOfSource_fiber
    (e : NativePlaces X.S ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (R : NativeImageRealizationSourceFields X I)
    (F : NativeFiberSourceFields X I e) :
    (nativePlaceBindingDonorsOfSource X I e R F).fiberMonEquiv =
      F.fiberMonEquiv :=
  rfl

/-- Exact named source obligation for the image realization at the native
selected place. -/
def NativeImageRealizationSourceObligation : Prop :=
  Nonempty (NativeImageRealizationSourceFields X I)

/-- Exact named source obligation for the native-selected-place fiber
equivalence. -/
def NativeFiberSourceObligation
    (e : NativePlaces X.S ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)) : Prop :=
  Nonempty (NativeFiberSourceFields X I e)

/-- The conditional binding exists whenever its two exact source obligations
are supplied. -/
theorem nativePlaceBindingDonorsOfSource_nonempty
    (e : NativePlaces X.S ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (hR : NativeImageRealizationSourceObligation X I)
    (hF : NativeFiberSourceObligation X I e) :
    Nonempty (NativePlaceBindingDonors X I) := by
  rcases hR with ⟨R⟩
  rcases hF with ⟨F⟩
  exact ⟨nativePlaceBindingDonorsOfSource X I e R F⟩

/-- The image obligation is exactly the missing R field of the native
binding, at the selected place badPlace X. -/
theorem nativeImageRealizationSourceObligation_iff :
    NativeImageRealizationSourceObligation X I ↔
      Nonempty (I.SourceImageRealization (nativeSelectedPlace X)) := by
  constructor
  . rintro ⟨R⟩
    exact ⟨nativeImageRealizationOfFields X I R⟩
  . rintro ⟨R⟩
    exact ⟨{ posRealAction := R.posRealAction, degree_of_q := R.degree_of_q }⟩

end LeanFormal.IUT.N8Closure.NativeBindingRFActual

end