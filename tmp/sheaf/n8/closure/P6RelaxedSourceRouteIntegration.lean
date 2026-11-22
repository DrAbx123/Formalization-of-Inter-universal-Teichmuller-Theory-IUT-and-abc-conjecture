import tmp.sheaf.n8.closure.P6AdmRedesign
import tmp.sheaf.n8.closure.P6GlobalLqDonorUnderconstrained
import tmp.sheaf.n8.closure.P6ChainA
import tmp.sheaf.n8.closure.P6Comparison

/-!
# Relaxed source route / corrected C9 target integration (Wave30)

Connects the actual P6AdmRedesign.RelaxedP6Readout to the corrected P6 source
route and C9 target.

The old frozen P6L.P6Readout route is not imported or used.  Relaxed route
obligations use the actual relaxed readout and an actual Chain A.  The actual
construction uses the formal constant GlobalLq Chain A (not source-global-L
evidence) and the actual relaxed readout; no free fields are introduced.

C9 corrected target:
- Q is Chain A's actual native q value (Q_eq_nativeScalar);
- Theta is the actual relaxed readout value;
- J range is still SourceAllowedOutput X, independent of Q <= Theta.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6RelaxedSourceRouteIntegration

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6ChainA
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.P6GlobalLqDonorUnderconstrained
open LeanFormal.IUT.N8Closure.P6AdmRedesign

universe u

variable {l : PrimeGeFive} {X : N8NativeInput l}
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable {mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v)}
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Relaxed P6 route obligations: actual Chain A + actual relaxed global
readout.  The frozen P6Readout route is not a field. -/
structure RelaxedRouteObligations (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)] where
  chainA : P6ChainAData X
  readout : RelaxedP6Readout X mu

namespace RelaxedRouteObligations

variable {X : N8NativeInput l}
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable {mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v)}
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
variable (R : RelaxedRouteObligations X mu)

/-- Q is the actual Chain A Q. -/
def Q : Real := R.chainA.Q

/-- Theta is the actual relaxed readout value. -/
def Theta : Real := R.readout.value

/-- Q is the actual native q scalar. -/
theorem Q_eq_nativeScalar : R.Q = qPilotSignedLog X := by
  calc
    R.Q = R.chainA.localData.scalar :=
      P6ChainA.Q_eq_localScalar (X := X) R.chainA
    _ = qPilotSignedLog X := R.chainA.localData.scalar_eq

/-- Theta is exactly the relaxed readout value. -/
theorem Theta_eq_readout : R.Theta = R.readout.value := rfl

end RelaxedRouteObligations

/-- Actual construction: formal constant Chain A + actual relaxed readout.
No frozen P6Readout and no free field. -/
noncomputable def relaxedRouteActual
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)] :
    RelaxedRouteObligations X mu where
  chainA := constantChainA X
  readout := P6AdmRedesign.relaxedP6Readout X mu

/-- The relaxed route obligations are actually inhabited. -/
theorem relaxedRouteObligations_actual
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)] :
    Nonempty (RelaxedRouteObligations X mu) :=
  ⟨relaxedRouteActual X mu⟩

/-- J type: actual source-allowed outputs, independent of Q <= Theta. -/
abbrev RelaxedJType (X : N8NativeInput l) :=
  SourceAllowedOutput X

/-- J range: all source-allowed outputs. -/
def RelaxedJRange (X : N8NativeInput l) : Set (RelaxedJType X) :=
  Set.univ

/-- Corrected C9 paper target over the relaxed route.  Only actual derived
Q/Theta and the fixed J range; no free Real/Set fields. -/
structure RelaxedC9PaperTarget (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)] where
  route : RelaxedRouteObligations X mu
  jRange_eq : RelaxedJRange X = Set.univ

/-- Corrected C9 target from a relaxed route. -/
def relaxedC9PaperTargetOfRoute
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    (R : RelaxedRouteObligations X mu) : RelaxedC9PaperTarget X mu where
  route := R
  jRange_eq := rfl

/-- Actual corrected C9 target: from the actual relaxed route. -/
theorem relaxedC9PaperTarget_actual
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)] :
    Nonempty (RelaxedC9PaperTarget X mu) :=
  ⟨relaxedC9PaperTargetOfRoute X mu (relaxedRouteActual X mu)⟩

/-- The corrected C9 target's Q is the native q scalar. -/
theorem relaxedC9PaperTarget_Q_eq_nativeScalar
    {X : N8NativeInput l}
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    {mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v)}
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    (T : RelaxedC9PaperTarget X mu) :
    T.route.Q = qPilotSignedLog X :=
  T.route.Q_eq_nativeScalar

end LeanFormal.IUT.N8Closure.P6RelaxedSourceRouteIntegration
