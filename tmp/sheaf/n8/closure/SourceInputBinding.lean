import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripComponentIdentification
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge
import Iut.Foundations.Frobenioid

/-!
# C1 stage 2 — SourcePlaceRealization / SourceInputBinding

Stage-2 type definitions for C1, frozen in `C1-STAGE1.md`.

`SourcePlaceRealization` records the actual place equivalence, the C1-selected
place `v`, its actual source image realization `R`, and the prime-strip fiber
comparison.  `SourceInputBinding` records only the place realization; the actual
global Frobenioid is a separate child obligation C1-g1 and is deliberately not
a free field.

Consumer: C2 actual local log/K1-K2, C3 prime-strip/theta-pilot data, C6
completion degrees/weights, C10 final assembly.

`sourceInputBinding_nonempty` is the only named-sorry declaration; it does not
create any place/data by a `noncomputable def := by sorry`.  Exact gaps:
C1-a place equivalence, C1-b fiber comparison, C1-d selected v/R, C1-e source
place selection, C1-g1 production Frobenioid, C1-c Prime/rho strip comparison.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.SourceInputBinding

universe ua uv upi umon ui uMon

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTII.Frobenioid.Example36

variable {l : PrimeGeFive} {V : Type uv}

/-- Actual local value group at a finite/infinite place, in the prime-strip
value-monoid form.  Finite branch is the production donor `finitePlaceValueGroup
= Multiplicative ℤ` (Example36PrimeStripBridge.lean:164); infinite branch is
`archimedeanValueGroup = Multiplicative ℝ` (Example36PrimeStripBridge.lean:483). -/
abbrev SourcePlaceValueGroup (F : Type ua) [Field F] [NumberField F]
    (P : NumberFieldPlaceIndex (F := F)) : Type :=
  match P with
  | Sum.inl _ => finitePlaceValueGroup
  | Sum.inr _ => archimedeanValueGroup

instance (F : Type ua) [Field F] [NumberField F]
    (P : NumberFieldPlaceIndex (F := F)) : CommMonoid (SourcePlaceValueGroup F P) := by
  cases P <;> infer_instance

/-- C1-a/b/d: actual place realization of the source input. -/
structure SourcePlaceRealization
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- Equivalence of the arbitrary source place type `V` with the actual
  finite/infinite places of `F := I.initial.arithmetic.Fmod`. -/
  placeEquiv : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)
  /-- The place selected by C1 for source log/pilot data. -/
  selected : V
  /-- Actual source image realization at the selected place (C1-d). -/
  selected_realization : I.SourceImageRealization selected
  /-- Comparison of each prime-strip fiber with the actual local value group
  at the corresponding place (C1-b). -/
  fiberMonEquiv : ∀ (n m : Int) (v : V),
    (I.primeStripAt n m).Mon v ≃*
      SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (placeEquiv v)

/-- C1 source binding: the actual place realization.  The global Frobenioid
is a separate child obligation C1-g1 and is deliberately NOT a free field here:
a `Nonempty` theorem must not fill an unconstrained Frobenioid datum. -/
structure SourceInputBinding
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- C1 place realization. -/
  place : SourcePlaceRealization I

/-- Exact C1 source-binding obligation: a place equivalence, a selected place,
its source image realization, and the prime-strip fiber comparison. This is
the missing source datum; it is not asserted as inhabited. -/
def SourceInputBindingObligation
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) : Prop :=
  Nonempty (SourceInputBinding I)

end LeanFormal.IUT.N8Closure.SourceInputBinding