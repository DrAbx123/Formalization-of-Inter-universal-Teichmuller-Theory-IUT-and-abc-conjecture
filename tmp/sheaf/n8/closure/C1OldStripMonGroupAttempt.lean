import tmp.sheaf.n8.closure.C1OldStripQuotientIdentificationAttempt
import tmp.sheaf.n8.closure.C1PlaceValueGroupActual

/-!
# C1OldStripMonGroupAttempt: units of old strip Mon vs actual PlaceUnitMonoid

`(I.primeStripAt n m).Mon v` is only a `CommMonoid`.  Its unit group
`(I.primeStripAt n m).Mon v)ˣ` is an actual group, but there is no production
equivalence from this unit group to the actual `PlaceUnitMonoid (e v)`.

This file records the actual unit-group construction and the exact missing
unit identification; the old kernel is defined only conditionally from that
identification.  No arbitrary group structure is added to `Mon`.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1OldStripMonGroupAttempt

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.C1OldStripQuotientIdentificationAttempt
open LeanFormal.IUT.N8Closure.C1PlaceValueGroupActual
open LeanFormal.IUT.N8Closure.C1ValueGroupActualAttempt
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} {V : Type uv} [Preorder V]

/-- Actual unit group of an old strip fiber (always a group). -/
abbrev OldStripUnitGroup
    (I : OldPlaceInput (l := l) (V := V)) (n m : Int) (v : V) : Type umon :=
  ((I.primeStripAt n m).Mon v)ˣ

/-- Exact missing unit-group identification to the actual place unit monoid. -/
structure C1OldStripUnitIdentification
    (I : OldPlaceInput (l := l) (V := V))
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)) where
  unitEquiv : ∀ (n m : Int) (v : V),
    OldStripUnitGroup I n m v ≃* PlaceUnitMonoid (e v)

def C1OldStripUnitIdentificationExists
    (I : OldPlaceInput (l := l) (V := V))
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)) : Prop :=
  Nonempty (C1OldStripUnitIdentification I e)

/-- Conditional old kernel on the actual unit group, pulled back from the
actual place kernel along the missing identification. -/
noncomputable def C1OldStripUnitIdentification.oldUnitKernel
    {I : OldPlaceInput (l := l) (V := V)}
    {e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)}
    (D : C1OldStripUnitIdentification I e) (n m : Int) (v : V) :
    Subgroup (OldStripUnitGroup I n m v) :=
  Subgroup.comap (D.unitEquiv n m v).toMonoidHom
    (placeUnitKernel (e v))

end LeanFormal.IUT.N8Closure.C1OldStripMonGroupAttempt