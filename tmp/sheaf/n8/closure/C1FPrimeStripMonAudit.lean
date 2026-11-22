import tmp.sheaf.n8.closure.C1OldStripQuotientIdentificationAttempt
import tmp.sheaf.n8.closure.C1OldStripMonGroupAttempt
import tmp.sheaf.n8.closure.C1PlaceValueGroupActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripComponentIdentification
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge

/-!
# C1FPrimeStripMonAudit: actual `FPrimeStrip.Mon` on `numberFieldPrimeStrip`

For the canonical `numberFieldPrimeStrip`, the `Mon` fiber is exactly the
actual `PlaceUnitMonoid`: finite component `(v.adicCompletion F)ˣ`, infinite
component `(w.Completion)ˣ`.  Thus on this constructor the Mon-level
identification is actual (not merely quotient).  For an arbitrary old
`OriginalInput`, no such identification exists and the exact named gap from
C1OldStrip... remains.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1FPrimeStripMonAudit

universe ua uv upi umon ui u v

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.C1ValueGroupActualAttempt
open LeanFormal.IUT.N8Closure.C1PlaceValueGroupActual
open LeanFormal.IUT.N8Closure.C1OldStripQuotientIdentificationAttempt
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open IsDedekindDomain
open scoped NumberField

variable {F : Type u} [Field F] [NumberField F]

/-- Canonical number-field prime strip `Mon` = actual place unit monoid. -/
theorem numberFieldPrimeStrip_Mon_eq_placeUnitMonoid
    (P : NumberFieldPlaceIndex (F := F)) :
    (numberFieldPrimeStrip (F := F)).Mon P = PlaceUnitMonoid (F := F) P := by
  cases P with
  | inl v => rfl
  | inr w => rfl

/-- Actual Mon-level equivalence for the canonical number-field prime strip. -/
noncomputable def canonicalFPrimeStripMonEquiv
    (P : NumberFieldPlaceIndex (F := F)) :
    (numberFieldPrimeStrip (F := F)).Mon P ≃* PlaceUnitMonoid (F := F) P := by
  cases P with
  | inl v => exact MulEquiv.refl _
  | inr w => exact MulEquiv.refl _

end LeanFormal.IUT.N8Closure.C1FPrimeStripMonAudit
