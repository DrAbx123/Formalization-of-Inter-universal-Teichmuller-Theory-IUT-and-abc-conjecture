import tmp.sheaf.n8.closure.PaperC9ComparisonAlias
import tmp.sheaf.n8.closure.PaperQLeThetaReduction
import tmp.sheaf.n8.closure.PaperValuesBoundedReduction

/-!
# Paper external gap reductions (Wave8c)

Two owner gaps are examined:

1. PaperQLeThetaReduction.missing_paperC9Comparison.  The alias version is
   proved from PaperC9ComparisonAlias.paperC9ComparisonAlias, which in turn calls
   the upstream named C9PaperClosure.paperC9Comparison.  No new sorry.

2. PaperValuesBoundedReduction.p6LReadoutBound_obligation.  It is attempted as a
   reduction to the P6Readout/Theta source relation

     forall R : P6Readout, R.ellOutValue <= C.theta.ellOutValue.

   This relation is definitionally the same as P6LReadoutBound (C.Theta is
   ThetaNamed C.theta), so the reduction is exact but does not remove the source
   bound: no production theorem supplies the relation.  Exact no-go for further
   reduction; the upstream named gap remains.

No owner file is edited.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperExternalGapReduction

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C9PaperClosure
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.PaperQLeThetaReduction
open LeanFormal.IUT.N8Closure.PaperValuesBoundedReduction

universe u

variable {l : PrimeGeFive}

/-- Alias version of the PaperQLeThetaReduction P6 comparison count: same type
as missing_paperC9Comparison, proved from the C9PaperClosure alias. -/
theorem missing_paperC9Comparison_alias
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
    (O : C9PaperClosure.PaperC9Output X mu) :
    P6Comparison.P6Exact X O.Q ∨ P6Comparison.P6Epsilon X O.Q :=
  PaperC9ComparisonAlias.paperC9ComparisonAlias X mu O

/-- P6Readout/Theta source relation: every P6 readout value is bounded by the
readout value of the selected C9 Theta source object. -/
def P6ReadoutThetaSourceRelation
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
    (C : C9PaperClosure.PaperC9Output X mu) : Prop :=
  ∀ R : P6L.P6Readout (X := X) (mu := mu),
    R.ellOutValue ≤ C.theta.ellOutValue

/-- Exact reduction of P6LReadoutBound to the P6Readout/Theta source relation.
Both sides are definitionally the same because C.Theta is
ThetaNamed C.theta = C.theta.ellOutValue. -/
theorem p6LReadoutBound_iff_p6ReadoutThetaSourceRelation
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
    (C : C9PaperClosure.PaperC9Output X mu) :
    P6LReadoutBound X mu C ↔
      P6ReadoutThetaSourceRelation X mu C :=
  Iff.rfl

/-- The source relation gives the P6L readout bound. -/
theorem p6LReadoutBound_of_sourceRelation
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
    (C : C9PaperClosure.PaperC9Output X mu)
    (h : P6ReadoutThetaSourceRelation X mu C) :
    P6LReadoutBound X mu C :=
  (p6LReadoutBound_iff_p6ReadoutThetaSourceRelation X mu C).mpr h

end LeanFormal.IUT.N8Closure.PaperExternalGapReduction
