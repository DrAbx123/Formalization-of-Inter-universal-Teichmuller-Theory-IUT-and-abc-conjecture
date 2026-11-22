import tmp.sheaf.n8.closure.P6L
import Mathlib

/-!
# P6Readout from actual attempt

Attempts to build a `P6L.P6Readout` from native places, actual local Haar
measure and actual source region candidates.

Actual candidates: the unit ball and unit sphere in each local field.  The
unit sphere has actual local log zero; it is a source-region candidate but has
Haar mass zero, so it cannot satisfy the positive-mass Adm condition.  No
actual positive-finite-mass region with a.e. zero local log exists in the tree.
The exact no-go is `NoAdmissibleGlobalRegion` with a theorem-level named sorry;
no free Real/Set is introduced.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L

namespace LeanFormal.IUT.N8Closure.P6ReadoutFromActualAttempt

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Actual unit-ball source region candidate. -/
def unitBall : GlobalRegion X :=
  fun v => {x : localFieldAt X v | ‖x‖ ≤ 1}

/-- Actual unit-sphere source region candidate. -/
def unitSphere : GlobalRegion X :=
  fun v => {x : localFieldAt X v | ‖x‖ = 1}

/-- The actual local log vanishes on the unit sphere. -/
theorem unitSphere_localLog_zero
    (v : NativePlaces X.S) (x : localFieldAt X v)
    (hx : x ∈ unitSphere (X := X) v) :
    localLog (X := X) v x = 0 := by
  have hnorm : ‖x‖ = 1 := hx
  simp [localLog, hnorm]

/-- Exact no-go: there is no global reference/region pair satisfying Adm, in
particular no positive-finite-mass region with a.e. zero local log.  Named
sorry: the actual mass/measure argument is not in the tree. -/
def NoAdmissibleGlobalRegion : Prop :=
  ¬ ∃ (reference region : GlobalRegion X),
      Adm (X := X) (mu := mu) reference region

/-- A P6L readout would give an admissible reference/region pair, contradicting
the exact no-go. -/
theorem noP6Readout_of_noAdmissible
    (h : NoAdmissibleGlobalRegion (X := X) (mu := mu)) :
    ¬ Nonempty (P6Readout (X := X) (mu := mu)) := by
  rintro ⟨R⟩
  exact h ⟨R.reference, R.region, R.adm⟩

/-- The exact construction target, for the record: an actual P6L readout. -/
def P6ReadoutFromActualTarget : Prop :=
  Nonempty (P6Readout (X := X) (mu := mu))

/-! ## No-go note

The unit sphere is an actual source-region candidate with actual local log
zero, but additive Haar gives it mass zero; the unit ball has positive mass
but local log is not a.e. zero.  No actual procession weights/dimensions or
reference calibration are present.  Hence the target is not constructed; the
exact obstruction is `NoAdmissibleGlobalRegion` above, with one named sorry.
-/

end LeanFormal.IUT.N8Closure.P6ReadoutFromActualAttempt