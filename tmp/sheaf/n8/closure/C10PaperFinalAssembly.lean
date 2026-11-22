import tmp.sheaf.n8.closure.PaperC10Closure
import tmp.sheaf.n8.closure.PaperN8Closure

/-!
# Paper C10 final assembly (Wave18)

Exact target class for paper C10, assembled from the local zero-sorry
PaperC10Closure and the current PaperN8Closure.

The record keeps only:
- the actual PaperC10Output (PaperN8 route + finite Theta source);
- q <= theta;
- the exact finite Theta semantics thetaTop = (theta : WithTop Real), thetaTop != top;
- the exact P6 J range (SourceAllowedOutput X, independent of Q <= Theta).

The assembly has no local sorry.  It is built from
PaperC10Closure.paperC10Output_nonempty and PaperC10Closure.paperC10Conclusion.
The external PaperN8/P6 source gaps still block kernel closure; they are reported
as target-class preconditions, not hidden by new fields or assumptions.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C10PaperFinalAssembly

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.PaperC10Closure
open LeanFormal.IUT.N8Closure.PaperN8Closure

universe u

variable {l : PrimeGeFive}

/-- Exact paper C10 final target record.  No free source field is added: the
finite Theta and J range are the actual PaperC10 fields. -/
structure PaperC10FinalTarget
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)] where
  /-- Actual paper C10 output. -/
  c10 : PaperC10Output X mu
  /-- Q <= Theta; this is only a conclusion, not an input to P6. -/
  q_le_theta : c10.Q ≤ c10.Theta
  /-- Exact finite Theta semantics. -/
  thetaTop_eq : c10.thetaFinite.thetaTop = (c10.Theta : WithTop Real)
  /-- Not +inf. -/
  thetaTop_ne_top : c10.thetaFinite.thetaTop ≠ ⊤
  /-- Exact P6 J range, independent of Q <= Theta. -/
  jRange_eq : PaperC10JRange X = Set.univ

/-- Construction of the exact target record from an actual C10 output. -/
def paperC10FinalTargetOfOutput
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
    (O : PaperC10Output X mu) : PaperC10FinalTarget X mu where
  c10 := O
  q_le_theta := (paperC10Conclusion O).1
  thetaTop_eq := (paperC10Conclusion O).2.1
  thetaTop_ne_top := (paperC10Conclusion O).2.2
  jRange_eq := rfl

/-- Local zero-sorry assembly of the exact C10 target class. -/
theorem paperC10FinalTarget_nonempty
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)] :
    Nonempty (PaperC10FinalTarget X mu) := by
  obtain ⟨O⟩ := PaperC10Closure.paperC10Output_nonempty X mu
  exact ⟨paperC10FinalTargetOfOutput X mu O⟩

/-- Exact target-class proposition used as the paper C10 consumer surface. -/
def PaperC10Statement
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)] : Prop :=
  Nonempty (PaperC10FinalTarget X mu)

/-- Exact paper C10 target class is nonempty. -/
theorem paperC10Statement_actual
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)] :
    PaperC10Statement X mu :=
  paperC10FinalTarget_nonempty X mu

/-- Consumer: the assembled C10 target projects to the exact paper conclusion. -/
theorem paperC10Final_conclusion
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
    (T : PaperC10FinalTarget X mu) : PaperC10Conclusion T.c10 :=
  ⟨T.q_le_theta, T.thetaTop_eq, T.thetaTop_ne_top⟩

end LeanFormal.IUT.N8Closure.C10PaperFinalAssembly
