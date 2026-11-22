import tmp.sheaf.n8.closure.P6EllOutBridgeCarrierAttempt
import tmp.sheaf.n8.closure.P6Comparison
import tmp.sheaf.n8.closure.P6L

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# P6Readout from SourceAllowedOutput attempt

Attempts to construct an actual `P6L.P6Readout` from the C4/T11/C6 data of a
`P6Comparison.SourceAllowedOutput`.  The source J lives on the C6 arithmetic
tensor block and supplies only a region plus hull containment; `P6Readout`
requires a global family over `NativePlaces X.S` with an actual `Adm`
reference/region, procession weights/dimensions, and positive finite local
mass.  No production map/weights/dimensions/Adm are available.

This file proves the exact projection/reduction and records the missing
construction as a theorem-level named gap.  No arbitrary Adm is assumed.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6EllOutBridgeCarrierAttempt

namespace LeanFormal.IUT.N8Closure.P6ReadoutCarrierFromSourceAllowedAttempt

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Exact per-J target: an actual P6Readout whose ellOut value is J.ellOut. -/
def ReadoutFromSourceAllowed
    (J : P6Comparison.SourceAllowedOutput X) : Prop :=
  ∃ R : P6L.P6Readout (X := X) (mu := mu), R.ellOutValue = J.ellOut

/-- Every P6Readout carries the actual Adm condition, not an arbitrary
admissibility predicate. -/
theorem readout_adm_projection
    (R : P6L.P6Readout (X := X) (mu := mu)) :
    P6L.Adm (X := X) (mu := mu) R.reference R.region :=
  R.adm

/-- Any readout obtained from a source-allowed J is an actual Adm readout. -/
theorem readoutFromSourceAllowed_adm
    (J : P6Comparison.SourceAllowedOutput X)
    (h : ReadoutFromSourceAllowed (X := X) (mu := mu) J) :
    ∃ R : P6L.P6Readout (X := X) (mu := mu),
      P6L.Adm (X := X) (mu := mu) R.reference R.region ∧
        R.ellOutValue = J.ellOut := by
  rcases h with ⟨R, hR⟩
  exact ⟨R, R.adm, hR⟩

/-- A family of per-J actual readouts yields the existential carrier map. -/
theorem carrierMapTarget_of_readoutFamily
    (h : ∀ J : P6Comparison.SourceAllowedOutput X,
      ReadoutFromSourceAllowed (X := X) (mu := mu) J) :
    CarrierMapTarget (X := X) (mu := mu) := by
  classical
  choose map hmap using h
  exact ⟨map, hmap⟩

end LeanFormal.IUT.N8Closure.P6ReadoutCarrierFromSourceAllowedAttempt

end
