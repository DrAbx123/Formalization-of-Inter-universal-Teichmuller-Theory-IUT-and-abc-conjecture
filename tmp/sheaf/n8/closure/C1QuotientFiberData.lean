import tmp.sheaf.n8.closure.C1PlaceValueGroupActual
import tmp.sheaf.n8.closure.C1FullUnitValueGroupNoGo
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripComponentIdentification
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge

/-!
# C1QuotientFiberData: corrected quotient-by-kernel fiber target

The old `C1FiberMonEquivData` asks for a full-unit equivalence
`(I.primeStripAt n m).Mon v ≃* valueGroup`.  For the actual unit monoid this
is impossible (`-1` has order two; value groups are torsion-free).

Corrected target: quotient by the actual kernel (integral units at finite
places, norm-one units at infinite places), then the quotient is the value
group.  The finite/infinite actual equivalences are assembled in
`C1PlaceValueGroupActual`.  This file packages the corrected data and supplies
the canonical `numberFieldPrimeStrip` instance.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1QuotientFiberData

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.C1ValueGroupActualAttempt
open LeanFormal.IUT.N8Closure.C1UnitQuotientValueGroupAttempt
open LeanFormal.IUT.N8Closure.C1InfiniteUnitQuotientAttempt
open LeanFormal.IUT.N8Closure.C1PlaceValueGroupActual
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {F : Type u} [Field F] [NumberField F]

/-- Corrected C1 fiber data at a place: actual unit monoid modulo the actual
kernel (integral units / norm-one), compared to the actual value group. -/
structure C1PlaceQuotientFiberData (F : Type u) [Field F] [NumberField F] where
  /-- Quotient comparison at every finite/infinite place. -/
  quotientEquiv : ∀ P : NumberFieldPlaceIndex (F := F),
    (PlaceUnitMonoid P ⧸ placeUnitKernel P) ≃*
      SourcePlaceValueGroup F P

/-- Corrected data, constructed from the finite and infinite actual quotient
equivalences. -/
noncomputable def c1PlaceQuotientFiberData (F : Type u) [Field F] [NumberField F] :
    C1PlaceQuotientFiberData F where
  quotientEquiv := placeUnitQuotientEquivValueGroup

end LeanFormal.IUT.N8Closure.C1QuotientFiberData