import tmp.sheaf.n8.closure.P6EllOutBridgeAttempt

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# P6 ellOut carrier map attempt

Searches for an actual carrier map
  (J : SourceAllowedOutput X) -> P6Readout (X:=X) (mu:=mu)
preserving `ellOut`.  The map is quantified existentially in the target, not
introduced as a free data field.

No production declaration constructs the required P6Readout from J: the P6
readout needs an admissible reference/region family, procession weights and
dimensions, while J supplies only its C4/T11/C6 output region and hull
containment.  The exact target is recorded as a named gap.
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
open LeanFormal.IUT.N8Closure.P6EllOutBridgeAttempt

namespace LeanFormal.IUT.N8Closure.P6EllOutBridgeCarrierAttempt

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Exact carrier-map target: a single choice of P6Readout for every
source-allowed output J, preserving the P6 ellOut value.  The map is
existentially quantified, not a free parameter. -/
def CarrierMapTarget : Prop :=
  ∃ map : (J : P6Comparison.SourceAllowedOutput X) →
      P6L.P6Readout (X := X) (mu := mu),
    ∀ J : P6Comparison.SourceAllowedOutput X,
      (map J).ellOutValue = J.ellOut

/-- The exact carrier map implies the pointwise P6 ellOut bridge. -/
theorem p6EllOutBridge_of_carrierMap
    (h : CarrierMapTarget (X := X) (mu := mu)) :
    P6EllOutBridge (X := X) (mu := mu) := by
  rcases h with ⟨map, hmap⟩
  intro J
  exact ⟨{ readout := map J, ellOut_eq := hmap J }⟩

/-- The pointwise bridge implies the exact carrier-map target (choice). -/
theorem carrierMapTarget_of_p6EllOutBridge
    (h : P6EllOutBridge (X := X) (mu := mu)) :
    CarrierMapTarget (X := X) (mu := mu) := by
  classical
  refine ⟨fun J => (Classical.choice (h J)).readout, ?_⟩
  intro J
  exact (Classical.choice (h J)).ellOut_eq

end LeanFormal.IUT.N8Closure.P6EllOutBridgeCarrierAttempt

end
