import tmp.sheaf.n8.closure.C9PaperClosure
import tmp.sheaf.n8.closure.P6L

/-!
# Paper ValuesBounded reduction

Attempted reduction of PaperN8Closure.paperValuesBounded:

  PaperN8Closure.paperValuesBounded C
    : C9PaperClosure.ValuesBounded C

to the explicit P6/P6L bridge

  forall R : P6L.P6Readout, R.ellOutValue <= C.Theta.

The equivalence is proved exactly (no sorry).  The explicit bridge itself has no
production donor, so it is kept as one named component obligation.  No owner
file is edited.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperValuesBoundedReduction

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.C9PaperClosure

universe u

variable {l : PrimeGeFive}

/-- Explicit P6/P6L bridge: every actual global P6 readout value is bounded by
the selected C9 Theta value. -/
def P6LReadoutBound
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
    (C : C9PaperClosure.PaperC9Output X mu) : Prop :=
  ∀ R : P6L.P6Readout (X := X) (mu := mu), R.ellOutValue ≤ C.Theta

/-- Exact reduction: C9PaperClosure.ValuesBounded is equivalent to the explicit
P6/P6L readout bound.  This is the reduction of the PaperN8 local gap; the
bridge is not derived from the current interfaces, it is isolated. -/
theorem valuesBounded_iff_p6LReadoutBound
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
    (C : C9PaperClosure.PaperC9Output X mu) :
    C9PaperClosure.ValuesBounded (X := X) (mu := mu) C ↔
      P6LReadoutBound X mu C := by
  constructor
  · intro h R
    exact h R.ellOutValue ⟨R, rfl⟩
  · intro h z hz
    rcases hz with ⟨R, rfl⟩
    exact h R

/-- Directional reduction: the explicit P6/P6L bridge implies the PaperN8
ValuesBounded statement. -/
theorem paperValuesBounded_of_p6LReadoutBound
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
    (C : C9PaperClosure.PaperC9Output X mu)
    (h : P6LReadoutBound X mu C) :
    C9PaperClosure.ValuesBounded (X := X) (mu := mu) C :=
  (valuesBounded_iff_p6LReadoutBound X mu C).mpr h

/-- Exact named bridge gap: the P6/P6L readout bound has no production donor.
It is strictly the remaining source/interface condition after the exact
reduction; no owner theorem is assumed. -/
theorem p6LReadoutBound_obligation
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
    (C : C9PaperClosure.PaperC9Output X mu) :
    P6LReadoutBound X mu C := by
  sorry

/-- PaperN8 ValuesBounded statement reduced through the explicit P6/P6L bridge.
This has the same statement as PaperN8Closure.paperValuesBounded but is proved
from the isolated bridge, not from a local a-priori bound. -/
theorem paperValuesBounded_viaP6L
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
    (C : C9PaperClosure.PaperC9Output X mu) :
    C9PaperClosure.ValuesBounded (X := X) (mu := mu) C :=
  paperValuesBounded_of_p6LReadoutBound X mu C
    (p6LReadoutBound_obligation X mu C)

end LeanFormal.IUT.N8Closure.PaperValuesBoundedReduction
