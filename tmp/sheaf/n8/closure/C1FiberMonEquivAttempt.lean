import tmp.sheaf.n8.closure.C1BridgeProof
import tmp.sheaf.n8.closure.NativeC1

/-!
# C1FiberMonEquivAttempt: missing R / fiberMonEquiv for NativePlaceBindingDonors

`NativePlaceBindingDonors` needs a selected place, `R : SourceImageRealization
selected`, and `fiberMonEquiv`.  NativeC1 supplies the selected place only for
`NativePlaces X.S`; for an old `OriginalInput` place type `V`, no R constructor
and no prime-strip fiber comparison donor exist.

The full missing data is packaged as `C1FiberMonEquivData` and its existence is
the sole named sorry.  A conditional no-go for empty `V` is proved.  No
arbitrary R or equivalence is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1FiberMonEquivAttempt

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36

variable {l : PrimeGeFive} {V : Type uv}

/-- Exact missing C1 binding data: selected v, source image realization R, and
the prime-strip fiber comparison. -/
structure C1FiberMonEquivData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)) where
  /-- Selected old-input place. -/
  selected : V
  /-- Actual source image realization at the selected place. -/
  selected_realization : I.SourceImageRealization selected
  /-- Actual prime-strip fiber comparison. -/
  fiberMonEquiv : ∀ (n m : Int) (v : V),
    (I.primeStripAt n m).Mon v ≃*
      SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (e v)

/-- Exact existence target for the missing R/fiber package. -/
def C1FiberMonEquivDataExists
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)) : Prop :=
  Nonempty (C1FiberMonEquivData I e)

/-- Reused NativeC1 selected place (for the native place type only). -/
noncomputable def nativeSelectedPlaceDonor {l : PrimeGeFive}
    (X : N8NativeInput l) : NativePlaces X.S :=
  badPlace X

/-- Reused NativeC1 place equivalence. -/
noncomputable def nativePlaceEquivDonor {l : PrimeGeFive}
    (X : N8NativeInput l) :
    NativePlaces X.S ≃ NumberFieldPlaceIndex (F := X.S.arithmetic.Fmod) :=
  nativePlaceIndexEquiv X

/-- Conditional exact no-go: empty old place type rules out the missing data. -/
theorem no_c1FiberMonEquivData_of_isEmpty
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (h : IsEmpty V) :
    IsEmpty (C1FiberMonEquivData I e) :=
  ⟨fun D => h.false D.selected⟩

end LeanFormal.IUT.N8Closure.C1FiberMonEquivAttempt