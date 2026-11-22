import tmp.sheaf.n8.closure.SourceInputBinding
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume

/-!
# S3-C1 actual SourceInputBinding: data-conditional construction

`SourcePlaceRealization` requires four actual data: a place equivalence, a
selected place, a source image realization at it, and a prime-strip fiber
comparison.  None of these is derivable from `OriginalInput` alone in the
current tree: `V` is an arbitrary type with no place equivalence, and no
constructor of `SourceImageRealization` is provided.

This file therefore provides the honest data-conditional constructor: given
exactly those four actual data, build `SourceInputBinding I` with no sorry.
It does NOT manufacture `placeEquiv`/`selected`/`R`/`fiberMonEquiv`, and it
does not assert an inhabitant of `C1ActualData I`.

Missing production declarations are recorded in C1-STAGE3.md.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1Actual

universe ua uv upi umon ui u

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36

variable {l : PrimeGeFive} {V : Type uv}

/-- The four actual C1 data required for one source input.  This is a
structure of source data, not a free conclusion: each field is the exact
object C1 must construct. -/
structure C1ActualData (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- Actual place equivalence. -/
  placeEquiv : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)
  /-- Selected actual place. -/
  selected : V
  /-- Actual source image realization at the selected place. -/
  selected_realization : I.SourceImageRealization selected
  /-- Actual prime-strip fiber comparison. -/
  fiberMonEquiv : ∀ (n m : Int) (v : V),
    (I.primeStripAt n m).Mon v ≃*
      SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (placeEquiv v)

/-- Convert the four actual data to C1's `SourcePlaceRealization`. -/
def C1ActualData.toPlaceRealization {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    (D : C1ActualData I) : SourcePlaceRealization I where
  placeEquiv := D.placeEquiv
  selected := D.selected
  selected_realization := D.selected_realization
  fiberMonEquiv := D.fiberMonEquiv

/-- Data-conditional actual constructor of `SourceInputBinding I`.  No sorry;
no arbitrary data is invented. -/
def sourceInputBindingOfActual
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (D : C1ActualData I) :
    SourceInputBinding I :=
  ⟨D.toPlaceRealization⟩

/-- The conditional constructor gives a real Nonempty once the four actual
data are supplied. -/
theorem sourceInputBinding_nonempty_of_actual
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (D : C1ActualData I) :
    Nonempty (SourceInputBinding I) :=
  ⟨sourceInputBindingOfActual I D⟩

end LeanFormal.IUT.N8Closure.C1Actual