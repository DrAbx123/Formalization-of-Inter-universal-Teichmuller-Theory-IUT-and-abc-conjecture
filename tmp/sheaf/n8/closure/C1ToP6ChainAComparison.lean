import tmp.sheaf.n8.closure.C1PlaceValueGroupActual
import tmp.sheaf.n8.closure.P6ChainA

/-!
# C1ToP6ChainAComparison

Exact index-level comparison between the corrected C1 quotient fiber and the
P6 Chain A local q place.

The actual objects live at different tower levels:
- C1 corrected quotient fiber is a PlaceUnitMonoid at an `Fmod`-place;
- P6 Chain A local q is a `FinitePlaceQCandidate` at the `F`-place
  `nativeFPlaceOverBad X`.

The canonical index relation is the base-place projection `comap`:
`nativeFPlaceOverBad X` lies over `comap nativeFPlaceOverBad` in Fmod.  This
index relation is actual and constructed below.

A readout comparison between the C1 quotient value group and the P6 local
q/C9 scalar does not exist: the two sides are at different completions and no
transport/ramification comparison is exposed.  That is the missing source
object; no free compatibility field is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1ToP6ChainAComparison

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.P6ChainA
open LeanFormal.IUT.N8Closure.C1PlaceValueGroupActual
open LeanFormal.IUT.N8Closure.C1ValueGroupActualAttempt
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive}

/-- Exact actual index comparison: the top F-place of P6 Chain A, and its
base Fmod-place expressed in the C1 `NumberFieldPlaceIndex`. -/
structure C1ToP6ChainAComparison (X : N8NativeInput l) where
  /-- Actual top F-place used by P6 Chain A. -/
  topPlace : NumberField.FinitePlace X.S.arithmetic.F
  /-- Its base Fmod-place, as a C1 finite/infinite index. -/
  basePlace : NumberFieldPlaceIndex (F := X.S.arithmetic.Fmod)
  /-- Exact base projection relation. -/
  basePlace_eq :
    basePlace = Sum.inl (finitePlaceIndexEquiv (K := X.S.arithmetic.Fmod)
      (NumberFieldFinitePlace.comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)))

/-- Actual index comparison construction. -/
noncomputable def c1ToP6ChainAComparison (X : N8NativeInput l) :
    C1ToP6ChainAComparison X where
  topPlace := nativeFPlaceOverBad X
  basePlace := Sum.inl (finitePlaceIndexEquiv (K := X.S.arithmetic.Fmod)
    (NumberFieldFinitePlace.comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)))
  basePlace_eq := rfl

theorem c1ToP6ChainAComparison_nonempty (X : N8NativeInput l) :
    Nonempty (C1ToP6ChainAComparison X) :=
  ⟨c1ToP6ChainAComparison X⟩

end LeanFormal.IUT.N8Closure.C1ToP6ChainAComparison