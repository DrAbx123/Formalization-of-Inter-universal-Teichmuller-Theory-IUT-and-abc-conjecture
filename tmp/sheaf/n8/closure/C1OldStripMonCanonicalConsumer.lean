import tmp.sheaf.n8.closure.C1QuotientConsumerProbe
import tmp.sheaf.n8.closure.C1FPrimeStripMonAudit

/-!
# C1OldStripMonCanonicalConsumer

Connects the canonical `numberFieldPrimeStrip` Mon identification (actual on
that constructor) to the `C1QuotientConsumerProbe` consumer.  The result is an
exact conditional: if an old `OriginalInput` over the place-index type has
the canonical number-field prime strip and selected place/R, the quotient
consumer exists.  Arbitrary old Input still has no such identification.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1OldStripMonCanonicalConsumer

universe ua uv upi umon ui u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.C1QuotientConsumerProbe
open LeanFormal.IUT.N8Closure.C1QuotientFiberData
open LeanFormal.IUT.N8Closure.C1FPrimeStripMonAudit
open LeanFormal.IUT.N8Closure.C1PlaceValueGroupActual
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} {F : Type u} [Field F] [NumberField F]

/-- Canonical old-strip identification: if the old input is over the canonical
place-index type, its arithmetic root is `F`, and all its theater strips are
`numberFieldPrimeStrip`, then the probe's old-strip identification exists. -/
theorem c1OldStripMonIdentification_of_canonical
    (I : OriginalInput.{ua, u, upi, umon, ui} l (NumberFieldPlaceIndex (F := F)))
    (hF : I.initial.arithmetic.Fmod = F)
    (hstrip : ∀ (n m : Int),
      I.primeStripAt n m = numberFieldPrimeStrip (F := F)) :
    Nonempty (C1QuotientConsumerProbe.C1OldStripMonIdentification
      I (Equiv.refl _)) := by
  rw [hF]
  refine ⟨{ monEquiv := fun n m v => ?_ }⟩
  rw [hstrip n m]
  exact canonicalFPrimeStripMonEquiv (F := F) v

/-- Exact conditional consumer existence: canonical old strip + selected place/R
gives the quotient consumer.  No arbitrary consumer is introduced. -/
theorem sourceInputBindingQuotient_of_canonical
    (I : OriginalInput.{ua, u, upi, umon, ui} l (NumberFieldPlaceIndex (F := F)))
    (hF : I.initial.arithmetic.Fmod = F)
    (hstrip : ∀ (n m : Int),
      I.primeStripAt n m = numberFieldPrimeStrip (F := F))
    (selected : NumberFieldPlaceIndex (F := F))
    (R : I.SourceImageRealization selected) :
    Nonempty (SourceInputBindingQuotient I (Equiv.refl _) selected R) := by
  obtain ⟨D⟩ := c1OldStripMonIdentification_of_canonical I hF hstrip
  exact ⟨sourceInputBindingQuotientOfIdent I (Equiv.refl _) selected R D⟩

end LeanFormal.IUT.N8Closure.C1OldStripMonCanonicalConsumer