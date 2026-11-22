import tmp.sheaf.n8.closure.C1FiberMonEquivAttempt
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripComponentIdentification
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge

/-!
# C1ValueGroupActualAttempt: actual unit -> value group comparisons

The actual finite/infinite place unit monoids are full unit groups
`(v.adicCompletion F)ˣ` / `(w.Completion)ˣ`, while the value groups are
`Multiplicative ℤ` / `Multiplicative ℝ`.  Production provides actual monoid
homomorphisms

  finitePlaceLocalValue : (v.adicCompletion F)ˣ →* Multiplicative ℤ
  infinitePlaceCompletionDegree : (w.Completion)ˣ →* Multiplicative ℝ,

but these are valuation/degree maps with integral-unit kernels, not
equivalences onto the value groups.  The requested `fiberMonEquiv` is an
isomorphism `Mon v ≃* valueGroupAt v`; no such isomorphisms exist in the tree.

This file records the actual comparison maps and the exact missing R/fiber
obligation as the sole named sorry.  No arbitrary equivalence is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1ValueGroupActualAttempt

universe u v w

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open IsDedekindDomain
open scoped NumberField

variable {F : Type u} [Field F] [NumberField F]

/-- Actual unit monoid over a finite/infinite place index. -/
abbrev PlaceUnitMonoid : NumberFieldPlaceIndex (F := F) → Type u
  | Sum.inl v => (v.adicCompletion F)ˣ
  | Sum.inr w => (w.Completion)ˣ

instance (P : NumberFieldPlaceIndex (F := F)) : CommMonoid (PlaceUnitMonoid (F := F) P) := by
  cases P <;> infer_instance

/-- Actual unit -> value-group comparison at a finite place: the classical
exponent `ν_v` with integral-unit kernel. -/
noncomputable def finiteUnitToValueGroup
    (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* finitePlaceValueGroup :=
  finitePlaceLocalValue (F := F) v

/-- Actual unit -> value-group comparison at an infinite place:
`-log ‖u‖` into the archimedean value group. -/
noncomputable def infiniteUnitToValueGroup
    (w : NumberField.InfinitePlace F) :
    (w.Completion)ˣ →* archimedeanValueGroup :=
  infinitePlaceCompletionDegree (F := F) w

/-- The actual comparison map at a finite/infinite place index. -/
noncomputable def placeUnitToValueGroup
    (P : NumberFieldPlaceIndex (F := F)) :
    PlaceUnitMonoid (F := F) P →* SourcePlaceValueGroup (F := F) P :=
  match P with
  | Sum.inl v => finiteUnitToValueGroup (F := F) v
  | Sum.inr w => infiniteUnitToValueGroup (F := F) w

/-- Kernel at a finite place is the integral units; actual donor. -/
theorem finiteUnitToValueGroup_ker
    (v : HeightOneSpectrum (𝓞 F)) :
    (finiteUnitToValueGroup (F := F) v).ker =
      (v.adicCompletionIntegers F).units :=
  finitePlacePrimeStripValueMap_ker (F := F) v

end LeanFormal.IUT.N8Closure.C1ValueGroupActualAttempt