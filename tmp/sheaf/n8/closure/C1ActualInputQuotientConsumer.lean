import tmp.sheaf.n8.closure.N8NativeClosure
import tmp.sheaf.n8.closure.C1QuotientFiberData
import tmp.sheaf.n8.closure.C1PlaceValueGroupActual

/-!
# C1ActualInputQuotientConsumer

Connects the corrected quotient fiber data directly to the native/actual
source input C1 consumer (`NativeC1Data`), not to an arbitrary old
`OriginalInput`.  Both components are actual and zero-sorry:

- `nativeC1Data X`: place equivalence, selected bad place, membership/comap;
- `c1PlaceQuotientFiberData`: actual quotient-by-kernel equivalences at all
  finite/infinite places.

No old-strip identification is required for this native consumer.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1ActualInputQuotientConsumer

universe ua uv upi umon ui u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeClosure
open LeanFormal.IUT.N8Closure.C1QuotientFiberData
open LeanFormal.IUT.N8Closure.C1PlaceValueGroupActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive}

/-- Actual native C1 quotient consumer: C1 native data plus the corrected
quotient-by-kernel fiber comparison over the same native arithmetic root. -/
structure NativeC1QuotientConsumer (X : N8NativeInput l) where
  /-- Actual native C1 place/selected data. -/
  c1 : NativeC1Data X
  /-- Corrected quotient fiber comparison at every place. -/
  quotient : C1PlaceQuotientFiberData (F := X.S.arithmetic.Fmod)

/-- Actual construction from `nativeC1Data` and the quotient fiber data. -/
noncomputable def nativeC1QuotientConsumer (X : N8NativeInput l) :
    NativeC1QuotientConsumer X where
  c1 := nativeC1Data X
  quotient := c1PlaceQuotientFiberData (F := X.S.arithmetic.Fmod)

/-- The native C1 quotient consumer is actually inhabited. -/
theorem nativeC1QuotientConsumer_nonempty (X : N8NativeInput l) :
    Nonempty (NativeC1QuotientConsumer X) :=
  ⟨nativeC1QuotientConsumer X⟩

end LeanFormal.IUT.N8Closure.C1ActualInputQuotientConsumer