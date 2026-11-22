import tmp.sheaf.n8.closure.UnitSphereReadoutDonorActual
import Mathlib

/-!
# P6Readout nonarchimedean unit-sphere attempt

Only non-archimedean native places are handled.  The actual unit sphere is
open and compact in the ultrametric local field, so additive Haar gives it
positive finite mass (`nonarch_unitSphere_mass_pos_lt_top`).  A full
`UnitSphereReadoutDonor` is constructed from actual mass plus an explicit
actual support/weight/dimension donor.  The archimedean branch is the existing
Wave8b no-go.  No arbitrary weight is chosen: the weight/dimension donor is the
named-sorry gap.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6ReadoutUnitSphereAttempt
open LeanFormal.IUT.N8Closure.UnitSphereReadoutDonorActual

namespace LeanFormal.IUT.N8Closure.P6ReadoutNonarchSphereAttempt

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, IsUltrametricDist (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
variable [∀ v : NativePlaces X.S, Measure.IsOpenPosMeasure (mu v)]
variable [∀ v : NativePlaces X.S, IsFiniteMeasureOnCompacts (mu v)]

/-- Actual nonarchimedean unit-sphere mass: positive and finite. -/
theorem nonarch_unitSphere_mass_pos_lt_top (v : NativePlaces X.S) :
    0 < mu v (unitSphere (X := X) v) ∧
      mu v (unitSphere (X := X) v) < ⊤ := by
  have hsphere : unitSphere (X := X) v =
      Metric.sphere (0 : localFieldAt X v) 1 := by
    ext x
    simp [unitSphere, Metric.sphere, dist_eq_norm]
  have hopen : IsOpen (unitSphere (X := X) v) := by
    rw [hsphere]
    exact IsUltrametricDist.isOpen_sphere (x := (0 : localFieldAt X v))
      (r := 1) one_ne_zero
  have hpos : 0 < mu v (unitSphere (X := X) v) := by
    refine Measure.measure_pos_of_nonempty_interior (mu v) ⟨1, ?_⟩
    rw [hopen.interior_eq]
    simp [unitSphere]
  have hlt : mu v (unitSphere (X := X) v) < ⊤ := by
    rw [hsphere]
    exact (isCompact_sphere (0 : localFieldAt X v) 1).measure_lt_top
  exact ⟨hpos, hlt⟩

/-- Explicit actual support/weight/dimension donor.  These are the remaining
actual procession data; no weight is chosen by this file. -/
structure ProcessionWeightDimensionDonor where
  support : Finset (NativePlaces X.S)
  weight : NativePlaces X.S → ℝ
  dimension : NativePlaces X.S → ℝ
  dimension_ne_zero : ∀ v, dimension v ≠ 0

/-- Conditional full UnitSphereReadoutDonor from actual mass and the explicit
weight/dimension donor. -/
def unitSphereReadoutDonorOfWeights
    (D : ProcessionWeightDimensionDonor (X := X)) :
    UnitSphereReadoutDonor (X := X) (mu := mu) where
  support := D.support
  weight := D.weight
  dimension := D.dimension
  dimension_ne_zero := D.dimension_ne_zero
  mass_pos := fun v => (nonarch_unitSphere_mass_pos_lt_top (X := X) (mu := mu) v).1
  mass_lt_top := fun v => (nonarch_unitSphere_mass_pos_lt_top (X := X) (mu := mu) v).2

/-- Exact missing actual procession data.  Named sorry: no production source
constructs the support/weights/dimensions. -/
def ProcessionWeightDimensionDonorExists : Prop :=
  Nonempty (ProcessionWeightDimensionDonor (X := X))

/-- Full actual donor existence, conditional on the weight/dimension donor. -/
def NonarchUnitSphereReadoutDonorExists : Prop :=
  Nonempty (UnitSphereReadoutDonor (X := X) (mu := mu))

theorem nonarchUnitSphereReadoutDonorExists_of_weights
    (h : ProcessionWeightDimensionDonorExists (X := X)) :
    NonarchUnitSphereReadoutDonorExists (X := X) (mu := mu) := by
  rcases h with ⟨D⟩
  exact ⟨unitSphereReadoutDonorOfWeights (X := X) (mu := mu) D⟩

/-- Conditional P6L readout from the full donor. -/
def P6ReadoutFromNonarchUnitSphere
    (D : UnitSphereReadoutDonor (X := X) (mu := mu)) :
    P6Readout (X := X) (mu := mu) :=
  P6Readout.ofUnitSphereDonor (X := X) (mu := mu) D

/-! ## Archimedean branch

Reused from Wave8b: `noUnitSphereReadoutDonor_of_archimedean` shows that an
archimedean native place blocks any full donor.  This file does not try to
construct the archimedean mass.
-/

end LeanFormal.IUT.N8Closure.P6ReadoutNonarchSphereAttempt
