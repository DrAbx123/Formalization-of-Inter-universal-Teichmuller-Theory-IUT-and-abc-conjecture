import tmp.sheaf.n8.closure.PaperN8NativeC1Adapter

/-!
# PaperN8WithC1Target

Target correction with an explicit C1 slot:

  PaperN8WithC1 X mu = paper : PaperN8Output X mu + c1 : NativeC1PaperRoute X.

Constructed from the actual `PaperN8NativeC1Adapter`; no free adapter field.

Compatibility: there is currently no actual relation between the P6
chain/C9 paper route and the native C1 quotient consumer; PaperN8Output has no
C1 slot and neither side exposes a comparison map.  Therefore no compatibility
field is fabricated.  A compatibility field may be added only after an actual
relation declaration exists; today it is an exact target gap, not data.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperN8WithC1Target

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C1NativeConsumerPaperRoute
open LeanFormal.IUT.N8Closure.PaperN8Closure
open LeanFormal.IUT.N8Closure.PaperN8NativeC1Adapter

variable {l : PrimeGeFive}

/-- Paper N8 output with an explicit native C1 slot.  No compatibility field:
no actual relation exists yet. -/
structure PaperN8WithC1 (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)] where
  /-- Explicit paper P6/C9 output slot. -/
  paper : PaperN8Output X mu
  /-- Explicit native C1 consumer slot. -/
  c1 : NativeC1PaperRoute X

/-- Actual target construction from the existing adapter. -/
noncomputable def paperN8WithC1 (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)] :
    PaperN8WithC1 X mu :=
  let A := paperN8NativeC1Adapter X mu
  { paper := A.paper, c1 := A.c1 }

theorem paperN8WithC1_nonempty (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)] :
    Nonempty (PaperN8WithC1 X mu) :=
  ⟨paperN8WithC1 X mu⟩

end LeanFormal.IUT.N8Closure.PaperN8WithC1Target