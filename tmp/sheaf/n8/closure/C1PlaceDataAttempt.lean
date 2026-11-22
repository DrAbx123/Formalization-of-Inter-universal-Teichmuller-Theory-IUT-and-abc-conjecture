import tmp.sheaf.n8.closure.C4ExistenceAttempt
import tmp.sheaf.n8.closure.NativeC1

/-!
# C1PlaceDataAttempt: actual C1PlaceData for C4

`C1PlaceData I` is `{ v : V, R : I.SourceImageRealization v }`.  NativeC1
supplies an actual selected place only for `NativePlaces X.S`, not for an
arbitrary old `OriginalInput` place type `V`; and no `SourceImageRealization`
constructor exists.  The actual constructor from explicit `v`/`R` is
zero-sorry; the full existence is a named obligation.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1PlaceDataAttempt

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open ABCBridge.N8.C4Actual

variable {l : PrimeGeFive} {V : Type uv}

/-- Actual C1 place data from explicit selected v and realization R. -/
noncomputable def c1PlaceDataOf
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V)
    (R : I.SourceImageRealization v) : C1PlaceData (I := I) where
  v := v
  R := R

/-- NativeC1 selected-place donor, reused for the native place type. -/
noncomputable def nativeSelectedPlaceDonor {l : PrimeGeFive}
    (X : N8NativeInput l) : NativePlaces X.S :=
  badPlace X

/-- NativeC1 place equivalence, reused. -/
noncomputable def nativePlaceEquivDonor {l : PrimeGeFive}
    (X : N8NativeInput l) :
    NativePlaces X.S ≃ NumberFieldPlaceIndex (F := X.S.arithmetic.Fmod) :=
  nativePlaceIndexEquiv X

/-- Conditional exact no-go: an empty place type rules out C1PlaceData. -/
theorem no_c1PlaceData_of_isEmpty
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (h : IsEmpty V) :
    IsEmpty (C1PlaceData (I := I)) :=
  ⟨fun D => h.false D.v⟩

end LeanFormal.IUT.N8Closure.C1PlaceDataAttempt