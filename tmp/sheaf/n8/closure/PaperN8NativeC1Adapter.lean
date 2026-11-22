import tmp.sheaf.n8.closure.C1NativeConsumerPaperRoute
import tmp.sheaf.n8.closure.PaperN8Closure

/-!
# PaperN8NativeC1Adapter

Attaches the actual `NativeC1PaperRoute` C1 layer to the current
`PaperN8Output`/`N8RouteObligations` paper route.

Decisive target correction: `PaperN8Output` and `N8RouteObligations` have no
C1 field/slot.  There is therefore no route-level compatibility relation to
prove, and this file does NOT invent one.  The adapter is external and
packages two actual objects over the same native input:

- `paper : PaperN8Output X mu` (P6 route obligations + C9 paper component);
- `c1 : NativeC1PaperRoute X` (native C1 quotient consumer).

To make C1 a real route dependency, `PaperN8Output`/`N8RouteObligations` would
need a new explicit C1 slot; that is a target correction, not a free field.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperN8NativeC1Adapter

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C1NativeConsumerPaperRoute
open LeanFormal.IUT.N8Closure.PaperN8Closure

variable {l : PrimeGeFive}

/-- External adapter attaching the actual native C1 layer to the paper N8
route over the same native input.  No compatibility field is invented because
the current P6 route has no C1 slot. -/
structure PaperN8NativeC1Adapter (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)] where
  /-- Actual paper N8 output. -/
  paper : PaperN8Output X mu
  /-- Actual native C1 paper-route layer. -/
  c1 : NativeC1PaperRoute X

/-- Actual adapter from the two actual nonempty constructions. -/
noncomputable def paperN8NativeC1Adapter (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)] :
    PaperN8NativeC1Adapter X mu where
  paper := Classical.choice (paperN8Closure_nonempty X mu)
  c1 := nativeC1PaperRoute X

theorem paperN8NativeC1Adapter_nonempty (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)] :
    Nonempty (PaperN8NativeC1Adapter X mu) :=
  ⟨paperN8NativeC1Adapter X mu⟩

end LeanFormal.IUT.N8Closure.PaperN8NativeC1Adapter