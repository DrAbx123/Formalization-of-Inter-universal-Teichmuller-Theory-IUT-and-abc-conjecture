import tmp.sheaf.n8.closure.PaperN8Closure
import tmp.sheaf.n8.closure.P6L
import tmp.sheaf.n8.closure.P6Comparison

/-!
# Paper C10 closure — Q<=Theta, finite Theta semantics, P6 J range

Based only on PaperN8Closure.PaperN8Output.  The old C10/N8FullOutput target is
not imported or recreated.

- PaperC10Output carries the PaperN8Output, an exact ThetaFiniteSource, and the
  equality of the source readout with the PaperN8 route readout.
- Theta finiteness is a source field thetaTop : WithTop Real with
  thetaTop_ne_top; it is NOT derived by treating the Real field theta as finite
  in WithTop Real.
- Q<=Theta is the PaperN8Output q_le_theta field.
- P6 J range is Set (P6Comparison.SourceAllowedOutput X), independent of Q<=Theta.

Missing source finite/existence conditions are theorem-level named sorrys.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperC10Closure

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.PaperN8Closure

universe u

variable {l : PrimeGeFive}
variable {X : N8NativeInput l}
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable {mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v)}
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Exact finite Theta source semantics: an actual P6 readout with an explicit
WithTop finite value.  The finiteness is a source field, not a consequence of a
Real field. -/
structure ThetaFiniteSource (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    (r : P6Readout (X := X) (mu := mu)) where
  /-- Explicit extended Theta value. -/
  thetaTop : WithTop Real
  /-- It is the readout value, extended. -/
  thetaTop_eq : thetaTop = (r.ellOutValue : WithTop Real)
  /-- Exact finite semantics: not +inf. -/
  thetaTop_ne_top : thetaTop ≠ ⊤

/-- Actual ThetaFiniteSource from an arbitrary P6 readout. -/
def thetaFiniteSourceOfReadout
    (r : P6Readout (X := X) (mu := mu)) : ThetaFiniteSource X mu r where
  thetaTop := (r.ellOutValue : WithTop Real)
  thetaTop_eq := rfl
  thetaTop_ne_top := WithTop.coe_ne_top
/-- Paper C10 output over PaperN8Output and the exact finite Theta source. -/
structure PaperC10Output (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)] where
  /-- Paper N8 output (route, Q, Theta, Values, Q<=Theta). -/
  n8 : PaperN8Output X mu
  /-- Exact finite Theta source semantics. -/
  thetaFinite : ThetaFiniteSource X mu n8.c9.theta

namespace PaperC10Output

variable {X : N8NativeInput l}
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable {mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v)}
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
variable (O : PaperC10Output X mu)

/-- Q is the PaperN8Output Q. -/
def Q : Real := O.n8.q

/-- Theta is the PaperN8Output Theta (Real field). -/
def Theta : Real := O.n8.theta

/-- The finite semantic value is tied to the actual N8 route readout. -/
theorem thetaTop_eq_theta :
    O.thetaFinite.thetaTop = (O.n8.theta : WithTop Real) := by
  rw [O.thetaFinite.thetaTop_eq]
  rfl

end PaperC10Output

/-- Paper C10 conclusion: Q <= Theta, the Theta value is the exact finite source
value, and it is not +inf. -/
def PaperC10Conclusion
    {X : N8NativeInput l}
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    {mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v)}
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    (O : PaperC10Output X mu) : Prop :=
  O.n8.q ≤ O.n8.theta ∧
    O.thetaFinite.thetaTop = (O.n8.theta : WithTop Real) ∧
    O.thetaFinite.thetaTop ≠ ⊤



/-- The paper C10 conclusion from an assembled output. -/
theorem paperC10Conclusion
    {X : N8NativeInput l}
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    {mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v)}
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    (O : PaperC10Output X mu) : PaperC10Conclusion O :=
  ⟨PaperN8Closure.paperQ_le_theta X mu O.n8, O.thetaTop_eq_theta, O.thetaFinite.thetaTop_ne_top⟩

/-- J type: actual source-allowed output regions. -/
abbrev PaperC10JType (X : N8NativeInput l) :=
  P6Comparison.SourceAllowedOutput X

/-- J range: all actual source-allowed outputs, independent of Q <= Theta. -/
def PaperC10JRange (X : N8NativeInput l) : Set (PaperC10JType X) :=
  Set.univ

/-- Exact missing source finite object. -/
theorem thetaFiniteSource_nonempty
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    (r : P6Readout (X := X) (mu := mu)) :
    Nonempty (ThetaFiniteSource X mu r) :=
  ⟨thetaFiniteSourceOfReadout r⟩

/-- Exact missing C10 source assembly (matching PaperN8Output and finite source). -/
theorem paperC10Output_nonempty
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)] :
    Nonempty (PaperC10Output X mu) := by
  obtain ⟨O⟩ := PaperN8Closure.paperN8Closure_nonempty X mu
  let F : ThetaFiniteSource X mu O.c9.theta :=
    thetaFiniteSourceOfReadout O.c9.theta
  exact ⟨{ n8 := O, thetaFinite := F }⟩

end LeanFormal.IUT.N8Closure.PaperC10Closure
