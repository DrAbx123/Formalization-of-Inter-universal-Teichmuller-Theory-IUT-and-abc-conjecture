import tmp.sheaf.n8.closure.C1QuotientFiberData
import tmp.sheaf.n8.closure.C1PlaceValueGroupActual
import tmp.sheaf.n8.closure.SourceInputBinding

/-!
# C1 quotient consumer probe

The corrected quotient target is

  C1PlaceQuotientFiberData F:
    forall P, PlaceUnitMonoid F P / placeUnitKernel F P
      ~=* SourcePlaceValueGroup F P

and c1PlaceQuotientFiberData F constructs it from the actual finite/infinite
quotient equivalences (zero sorry).

This file connects that target to a quotient version of the C1
SourceInputBinding consumer.  The missing source link is the old-strip
identification

  forall n m v, (I.primeStripAt n m).Mon v ~=* PlaceUnitMonoid F (e v).

Only CommMonoid is available on an arbitrary old fiber; no Group/kernel is
available to form an old-Mon quotient directly.  Therefore the quotient
comparison is kept on the actual PlaceUnitMonoid side, and the old-strip
identification is one exact named gap.  No arbitrary kernel/equivalence is
introduced.

Affected N8 consumers: C1 SourceInputBinding users (C2, C3, C6, C7, C8, C9,
C10 and the native bridge/full-unit consumers) currently use the old full-unit
fiberMonEquiv; they must switch to this quotient consumer plus the old-strip
identification.  The old target and other owner files are not edited.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1QuotientConsumerProbe

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.C1PlaceValueGroupActual
open LeanFormal.IUT.N8Closure.C1QuotientFiberData
open LeanFormal.IUT.N8Closure.C1ValueGroupActualAttempt
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open IsDedekindDomain
open scoped NumberField

universe ua uv upi umon ui u

variable {l : PrimeGeFive}
variable {V : Type uv}

/-- Exact missing old-strip identification with the actual place unit monoid. -/
structure C1OldStripMonIdentification
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)) where
  monEquiv : ∀ (n m : Int) (v : V),
    (I.primeStripAt n m).Mon v ≃*
      PlaceUnitMonoid (F := I.initial.arithmetic.Fmod) (e v)

/-- Quotient version of the C1 SourceInputBinding consumer: selected place and
R, the missing old-strip identification, and the actual quotient comparison on
the units side. -/
structure SourceInputBindingQuotient
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (selected : V)
    (R : I.SourceImageRealization selected) where
  /-- Missing old-strip-to-PlaceUnitMonoid identification. -/
  oldStripId : C1OldStripMonIdentification I e
  /-- Actual quotient-by-kernel comparison at every place. -/
  quotientData : C1PlaceQuotientFiberData (F := I.initial.arithmetic.Fmod)

/-- Construct the quotient consumer from the old-strip identification and the
actual, zero-sorry quotient data. -/
noncomputable def sourceInputBindingQuotientOfIdent
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (selected : V) (R : I.SourceImageRealization selected)
    (D : C1OldStripMonIdentification I e) :
    SourceInputBindingQuotient I e selected R where
  oldStripId := D
  quotientData := c1PlaceQuotientFiberData (F := I.initial.arithmetic.Fmod)

/-- Exact named gap: the old-strip-to-PlaceUnitMonoid identification. -/
theorem c1OldStripMonIdentification_nonempty
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)) :
    Nonempty (C1OldStripMonIdentification I e) := by
  sorry

/-- Quotient consumer existence from the named old-strip gap. -/
theorem sourceInputBindingQuotient_nonempty
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (selected : V) (R : I.SourceImageRealization selected) :
    Nonempty (SourceInputBindingQuotient I e selected R) := by
  obtain ⟨D⟩ := c1OldStripMonIdentification_nonempty I e
  exact ⟨sourceInputBindingQuotientOfIdent I e selected R D⟩

end LeanFormal.IUT.N8Closure.C1QuotientConsumerProbe
