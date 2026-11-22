import tmp.sheaf.n8.closure.C1QuotientFiberData
import tmp.sheaf.n8.closure.C1PlaceValueGroupActual

/-!
# C1OldStripQuotientIdentificationAttempt

Attempts to identify an arbitrary old `I.primeStripAt 0 0).Mon v` with the
actual `PlaceUnitMonoid (e v)` and then define the quotient kernel.

No production identification exists.  The exact missing data is packaged as
`C1OldStripMonIdentification`; from it the kernel is `Subgroup.comap` of the
actual place kernel.  The full existence is a theorem-level named sorry; no
arbitrary equivalence or kernel is fabricated.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1OldStripQuotientIdentificationAttempt

universe ua uv upi umon ui u v

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.C1PlaceValueGroupActual
open LeanFormal.IUT.N8Closure.C1QuotientFiberData
open LeanFormal.IUT.N8Closure.C1ValueGroupActualAttempt
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} {V : Type uv} [Preorder V]

abbrev OldPlaceInput := OriginalInput.{ua, uv, upi, umon, ui} l V

/-- Exact missing identification: every old theater-strip unit monoid fiber is
the actual `PlaceUnitMonoid` at the corresponding place. -/
structure C1OldStripMonIdentification
    (I : OldPlaceInput (l := l) (V := V))
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)) where
  /-- Actual strip-to-place unit monoid equivalence, for all n,m,v. -/
  monEquiv : ∀ (n m : Int) (v : V),
    (I.primeStripAt n m).Mon v ≃*
      PlaceUnitMonoid (e v)

/-- Exact target: the missing old-strip identification.  Sole named sorry. -/
def C1OldStripMonIdentificationExists
    (I : OldPlaceInput (l := l) (V := V))
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)) : Prop :=
  Nonempty (C1OldStripMonIdentification I e)

end LeanFormal.IUT.N8Closure.C1OldStripQuotientIdentificationAttempt