import tmp.sheaf.n8.closure.P6L
import Mathlib

/-!
# P6L actual readout attempt

Attempts to construct an actual `P6L.P6Readout` from the native places,
`localFieldAt`, an actual local Haar measure and a reference region.

Actual available: native place family, local fields, global region type, local
log `Real.log ‖x‖`, and the Haar measure parameter.

Not available as actual data: admissible regions with positive finite Haar
mass and almost-everywhere zero local log, procession weights/dimensions, and
a reference calibration.  The target is exactly `Nonempty (P6Readout ...)`;
it is registered with a theorem-level named sorry.  No free Real/Set field.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L

namespace LeanFormal.IUT.N8Closure.P6LActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- The actual local log readout is the P6L one, not a new function. -/
theorem actualLocalLog_eq (v : NativePlaces X.S) (x : localFieldAt X v) :
    localLog (X := X) v x = Real.log ‖x‖ := rfl

/-- The global carrier/region types are exactly P6L's, over NativePlaces and
localFieldAt. -/
abbrev actualGlobalCarrier : Type _ := GlobalCarrier (X := X)
abbrev actualGlobalRegion : Type _ := GlobalRegion (X := X)

/-- Exact actual P6 readout target: an actual instance of P6L.P6Readout with
the actual local Haar measure.  This is not a free field; it is the existing
P6L interface type. -/
def P6LActualReadoutTarget : Prop :=
  Nonempty (P6Readout (X := X) (mu := mu))

theorem P6LActualReadoutTarget_iff_p6ReadoutExists :
    P6LActualReadoutTarget (X := X) (mu := mu) ↔
      p6ReadoutExists (X := X) (mu := mu) :=
  Iff.rfl

/-! ## No-go note

Candidates checked:
- the full local field has no finite positive Haar mass;
- a unit/norm-one region has zero Haar mass for the additive Haar measure and
  no a.e.-zero-local-log positive-mass region is constructed in the tree;
- no actual procession weight/dimension/reference data exists.

Therefore the actual construction is not supplied here; the exact target is
registered as the named sorry above.  No arbitrary Set/Real or fake data is
introduced.
-/

end LeanFormal.IUT.N8Closure.P6LActual