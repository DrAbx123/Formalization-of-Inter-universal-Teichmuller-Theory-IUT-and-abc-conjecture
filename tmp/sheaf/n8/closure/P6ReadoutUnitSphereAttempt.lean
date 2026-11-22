import tmp.sheaf.n8.closure.P6L
import Mathlib

/-!
# P6Readout unit-sphere attempt

Attempts to use the actual unit sphere `{x | ‖x‖ = 1}` as both reference and
region for `P6L.P6Readout`.

Actual: the unit sphere is a measurable source-region candidate and the local
log vanishes on it pointwise.  The remaining actual data are the Haar mass
`0 < μ(sphere) < top` and the procession weights/dimensions.  A conditional
constructor `P6Readout.ofUnitSphereDonor` builds the actual readout from those
donors; the donor's nonemptiness is the named sorry.  No arbitrary weight is
chosen by this file.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L

namespace LeanFormal.IUT.N8Closure.P6ReadoutUnitSphereAttempt

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Unit sphere as a global region candidate (norm = 1 at every place). -/
def unitSphere : GlobalRegion X :=
  fun v => {x : localFieldAt X v | ‖x‖ = 1}

theorem unitSphere_localLog_zero
    (v : NativePlaces X.S) (x : localFieldAt X v)
    (hx : x ∈ unitSphere (X := X) v) :
    localLog (X := X) v x = 0 := by
  have hnorm : ‖x‖ = 1 := hx
  simp [localLog, hnorm]

theorem unitSphere_measurable (v : NativePlaces X.S) :
    MeasurableSet (unitSphere (X := X) v) := by
  have hclosed : IsClosed {x : localFieldAt X v | ‖x‖ = 1} := by
    exact isClosed_singleton.preimage continuous_norm
  exact hclosed.measurableSet

/-- Exact actual donor needed to make the unit sphere an admissible reference
and region: positive finite Haar mass at every place and actual procession
weights/dimensions.  No weight is chosen here. -/
structure UnitSphereReadoutDonor where
  support : Finset (NativePlaces X.S)
  weight : NativePlaces X.S → ℝ
  dimension : NativePlaces X.S → ℝ
  dimension_ne_zero : ∀ v, dimension v ≠ 0
  mass_pos : ∀ v, 0 < mu v (unitSphere (X := X) v)
  mass_lt_top : ∀ v, mu v (unitSphere (X := X) v) < ⊤

/-- Conditional actual P6L readout: unit sphere as reference and region, with
donor-supplied weights/dimensions and Haar mass.  No arbitrary weight is
introduced by this constructor. -/
def P6Readout.ofUnitSphereDonor
    (D : UnitSphereReadoutDonor (X := X) (mu := mu)) :
    P6Readout (X := X) (mu := mu) where
  support := D.support
  weight := D.weight
  dimension := D.dimension
  dimension_ne_zero := D.dimension_ne_zero
  reference := unitSphere (X := X)
  region := unitSphere (X := X)
  adm := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v; exact unitSphere_measurable (X := X) v
    · intro v; exact D.mass_pos v
    · intro v; exact D.mass_lt_top v
    · intro v; exact Filter.Eventually.of_forall
        (fun x hx => unitSphere_localLog_zero (X := X) v x hx)
    · intro v; exact unitSphere_measurable (X := X) v
    · intro v; exact D.mass_pos v
    · intro v; exact D.mass_lt_top v
    · intro v; exact Filter.Eventually.of_forall
        (fun x hx => unitSphere_localLog_zero (X := X) v x hx)
  value := ellOut (X := X) (mu := mu) D.support D.weight D.dimension
    (unitSphere (X := X)) (unitSphere (X := X))
  value_eq := rfl

/-- Exact donor existence target.  Named sorry: actual positive finite
p-adic/archimedean unit-sphere masses and actual procession weights/dimensions
are not supplied by a production constructor in the tree. -/
def UnitSphereReadoutDonorExists : Prop :=
  Nonempty (UnitSphereReadoutDonor (X := X) (mu := mu))

/-- Exact readout target, inhabited as soon as the donor exists. -/
def P6ReadoutFromUnitSphereTarget : Prop :=
  Nonempty (P6Readout (X := X) (mu := mu))

theorem P6ReadoutFromUnitSphereTarget_of_donor
    (h : UnitSphereReadoutDonorExists (X := X) (mu := mu)) :
    P6ReadoutFromUnitSphereTarget (X := X) (mu := mu) := by
  rcases h with ⟨D⟩
  exact ⟨P6Readout.ofUnitSphereDonor (X := X) (mu := mu) D⟩

end LeanFormal.IUT.N8Closure.P6ReadoutUnitSphereAttempt
