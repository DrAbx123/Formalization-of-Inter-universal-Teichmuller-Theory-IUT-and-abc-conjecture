import tmp.sheaf.n8.closure.C1OldStripMonGroupAttempt
import tmp.sheaf.n8.closure.NativeC1

/-!
# C1OldStripUnitIdentificationSourceAttempt

Source search for an actual identification
`((I.primeStripAt n m).Mon v)ˣ ≃* PlaceUnitMonoid (e v)`.

Production `I.primeStripAt` is an arbitrary `FPrimeStrip`; its `Mon` fiber is
only a `CommMonoid` field with no comparison to the native place completion or
to `numberFieldPrimeStrip`.  NativeC1 supplies actual places for the native
root, not for an arbitrary old `OriginalInput` V.  Therefore the identification
remains the exact named obligation; no equivalence is manufactured.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1OldStripUnitIdentificationSourceAttempt

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.C1OldStripQuotientIdentificationAttempt
open LeanFormal.IUT.N8Closure.C1OldStripMonGroupAttempt
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} {V : Type uv} [Preorder V]

end LeanFormal.IUT.N8Closure.C1OldStripUnitIdentificationSourceAttempt