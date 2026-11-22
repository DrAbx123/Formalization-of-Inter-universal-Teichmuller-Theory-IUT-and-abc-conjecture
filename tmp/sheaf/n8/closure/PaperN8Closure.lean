import tmp.sheaf.n8.closure.N8RouteClosure
import tmp.sheaf.n8.closure.C9PaperClosure
import tmp.sheaf.n8.closure.PaperQLeThetaReduction
import tmp.sheaf.n8.closure.PaperValuesBoundedReduction

/-!
# Paper N8 closure (audit-corrected)

This is the current paper N8 route assembly:

- p6RouteObligations : N8RouteClosure.N8RouteObligations X mu.  This is a P6
  obligation package, NOT a constructed source closure: its chainB field is the
  Prop MissingSLToCompleteAlpha and its hull field is an abstract P6HullSetup
  filled by a named gap.
- c9 : C9PaperClosure.PaperC9Output X mu.  q/theta/values are derived from this
  C9 component; ValuesBounded and Q<=Theta are separate theorems below, not
  fields of PaperN8Output.

J independence is carried by the P6 route comparison inside
N8RouteObligations; no Q<=Theta input is used.  Q<=Theta is only a theorem
conclusion.  Legacy N8FullOutput/legacy C10 is not imported.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperN8Closure

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.N8RouteClosure
open LeanFormal.IUT.N8Closure.P6ChainA
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.C9PaperClosure
open LeanFormal.IUT.N8Closure.PaperQLeThetaReduction
open LeanFormal.IUT.N8Closure.C9QPilotRegion

universe u

variable {l : PrimeGeFive}

/-- Paper N8 target: P6 obligation package + C9 paper component. -/
structure PaperN8Output
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)] where
  /-- P6 obligation package (not a source closure). -/
  p6RouteObligations : N8RouteObligations X mu
  /-- C9 Q/Theta/Values component. -/
  c9 : C9PaperClosure.PaperC9Output X mu

namespace PaperN8Output

variable {X : N8NativeInput l}
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable {mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v)}
variable [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
variable (O : PaperN8Output X mu)

/-- Paper q, derived from the C9 component. -/
def q : Real := C9PaperClosure.PaperC9Output.Q O.c9

/-- Paper theta, derived from the C9 component. -/
def theta : Real := C9PaperClosure.PaperC9Output.Theta O.c9

/-- Paper values, derived from the C9 component. -/
def values : Set Real := C9PaperClosure.PaperC9Output.valuesSet O.c9

/-- q is the actual native q scalar. -/
theorem q_eq_nativeScalar : O.q = qPilotSignedLog X :=
  C9PaperClosure.PaperC9Output.Q_eq_nativeScalar O.c9

/-- q is also the P6 route's Chain A Q. -/
theorem q_eq_route : O.q = O.p6RouteObligations.chainA.Q := by
  calc
    O.q = qPilotSignedLog X := O.q_eq_nativeScalar
    _ = O.p6RouteObligations.chainA.localData.scalar :=
      (O.p6RouteObligations.chainA.localData.scalar_eq).symm
    _ = O.p6RouteObligations.chainA.Q :=
      (P6ChainA.Q_eq_localScalar (X := X) O.p6RouteObligations.chainA).symm

end PaperN8Output

/-- Exact C9 ValuesBounded gap for the paper route. -/
theorem paperValuesBounded
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
    (C : C9PaperClosure.PaperC9Output X mu) :
    C9PaperClosure.ValuesBounded (X := X) (mu := mu) C :=
  PaperValuesBoundedReduction.paperValuesBounded_of_p6LReadoutBound X mu C
    (PaperValuesBoundedReduction.p6LReadoutBound_obligation X mu C)

/-- Exact C9 Q<=Theta gap for the paper route.  This is the conclusion, not an
input to the P6 comparison. -/
theorem paperQLeTheta
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
    (C : C9PaperClosure.PaperC9Output X mu) :
    C9PaperClosure.QInRleqTheta (X := X) (mu := mu) C := by
  have hVB : C9PaperClosure.ValuesBounded (X := X) (mu := mu) C :=
    paperValuesBounded X mu C
  have hbridge : P6EllOutInValues (X := X) (mu := mu) C :=
    missing_p6EllOutInValues (X := X) (mu := mu) C
  have hcomp : P6Comparison.P6Exact X C.Q ∨ P6Comparison.P6Epsilon X C.Q :=
    missing_paperC9Comparison (X := X) (mu := mu) C
  have hle : C.Q ≤ C.Theta :=
    paperQLeTheta_of_comparison_valuesBounded (X := X) (mu := mu) C hVB hbridge hcomp
  exact (C9PaperClosure.qInRleqTheta_iff (X := X) (mu := mu) C).mpr hle

/-- Final paper Q <= Theta, derived from the exact C9 QInRleqTheta gap. -/
theorem paperQ_le_theta
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
    (O : PaperN8Output X mu) : O.q ≤ O.theta := by
  have h := paperQLeTheta X mu O.c9
  exact (C9PaperClosure.qInRleqTheta_iff (X := X) (mu := mu) O.c9).mp h

/-- Assembly of the paper N8 target from the P6 route and C9 paper component.
No local named sorry remains; paperValuesBounded is reduced through
PaperValuesBoundedReduction and paperQLeTheta through PaperQLeThetaReduction. -/
theorem paperN8Closure_nonempty
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)] :
    Nonempty (PaperN8Output X mu) := by
  obtain ⟨O⟩ := n8RouteObligations_nonempty X mu
  obtain ⟨C⟩ := C9PaperClosure.paperC9Output_nonempty X mu
  exact ⟨{ p6RouteObligations := O, c9 := C }⟩

end LeanFormal.IUT.N8Closure.PaperN8Closure
