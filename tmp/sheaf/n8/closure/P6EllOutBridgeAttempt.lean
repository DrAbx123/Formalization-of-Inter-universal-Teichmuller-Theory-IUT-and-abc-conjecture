import tmp.sheaf.n8.closure.C9PaperClosure
import tmp.sheaf.n8.closure.P6Comparison
import tmp.sheaf.n8.closure.P6L

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# P6 ellOut -> paper Values bridge attempt

`P6EllOutInValues O` asks that every source-allowed P6 ellOut value is an
element of the paper Values set.  The paper Values set is built from
`P6L.P6Readout`, while P6 ellOut is computed from `SourceAllowedOutput`
(C4/T11/C6 data).  The two carriers are not identified by the current
interfaces.

This file proves the exact conditional reduction from a per-J paper readout
carrier, and records the missing carrier map as a theorem-level named gap.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C9QThetaValuesNamed
open LeanFormal.IUT.N8Closure.C9PaperClosure
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.P6L

namespace LeanFormal.IUT.N8Closure.P6EllOutBridgeAttempt

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]


/-- Local form of the P6 ellOut membership (same body as the reduction file; the
import is split to avoid a cycle). -/
def P6EllOutInValues (O : PaperC9Output (X := X) mu) : Prop :=
  ∀ J : P6Comparison.SourceAllowedOutput X,
    J.ellOut ∈ PaperC9Output.valuesSet (X := X) (mu := mu) O

/-- Exact per-J bridge: a paper P6 readout whose ellOut value is the P6
source-allowed ellOut value.  No equality to Q or Q<=Theta. -/
structure SourceAllowedToPaperReadout (J : P6Comparison.SourceAllowedOutput X) where
  readout : P6L.P6Readout (X := X) (mu := mu)
  ellOut_eq : readout.ellOutValue = J.ellOut

/-- Global bridge: every source-allowed J has an exact paper readout carrier. -/
def P6EllOutBridge : Prop :=
  ∀ J : P6Comparison.SourceAllowedOutput X,
    Nonempty (SourceAllowedToPaperReadout (X := X) (mu := mu) J)

/-- Conditional proof of `P6EllOutInValues` from the exact per-J carrier map. -/
theorem p6EllOutInValues_of_bridge
    (O : PaperC9Output (X := X) mu)
    (h : P6EllOutBridge (X := X) (mu := mu)) :
    P6EllOutInValues (X := X) (mu := mu) O := by
  intro J
  rcases h J with ⟨K⟩
  refine ⟨K.readout, ?_⟩
  exact K.ellOut_eq.symm

/-- Exact missing carrier map.  No production construction maps a
`SourceAllowedOutput` J to a `P6L.P6Readout` with matching ellOut. -/
theorem missing_p6EllOutBridge :
    P6EllOutBridge (X := X) (mu := mu) := by
  sorry

/-- The previously named `missing_p6EllOutInValues` is reduced to the exact
carrier bridge; this does not promote it to actual without the named bridge. -/
theorem p6EllOutInValues_via_bridge
    (O : PaperC9Output (X := X) mu) :
    P6EllOutInValues (X := X) (mu := mu) O :=
  p6EllOutInValues_of_bridge (X := X) (mu := mu) O
    (missing_p6EllOutBridge (X := X) (mu := mu))

end LeanFormal.IUT.N8Closure.P6EllOutBridgeAttempt

end