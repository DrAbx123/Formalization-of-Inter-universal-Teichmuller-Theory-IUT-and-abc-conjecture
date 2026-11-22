import tmp.sheaf.n8.closure.P6ReadoutUnitSphereAttempt
import Mathlib

/-!
# Unit-sphere readout donor: actual attempt

Reuses the Wave8 unit sphere and `UnitSphereReadoutDonor`.  The unit sphere is
measurable and has zero local log pointwise.  The actual mass and
weights/dimensions are the blockers: at an archimedean native place the
additive Haar unit sphere has measure zero, so a donor with `0 < mu (unitSphere)`
cannot exist there.  The archimedean zero-mass fact is the named sorry; the
conditional no-go is proved from it.  No arbitrary weight is chosen.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6ReadoutUnitSphereAttempt

namespace LeanFormal.IUT.N8Closure.UnitSphereReadoutDonorActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- A native selected place that is archimedean over the base. -/
def HasArchimedeanNativePlace : Prop :=
  ∃ v : NativePlaces X.S,
    NumberFieldPlace.IsInfinite
      (NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) v.1)

/-- Exact archimedean obstruction: the additive Haar mass of the norm-one
sphere at an archimedean native place is zero.  Named sorry: production has
no instance theorem for the native `localFieldAt` archimedean branch. -/
theorem archimedean_unitSphere_mass_zero
    (v : NativePlaces X.S)
    (hv : NumberFieldPlace.IsInfinite
      (NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) v.1)) :
    mu v (unitSphere (X := X) v) = 0 := by
  sorry

/-- No unit-sphere readout donor exists when an archimedean native place is
present: its required positive unit-sphere mass contradicts the zero mass. -/
theorem noUnitSphereReadoutDonor_of_archimedean
    (h : HasArchimedeanNativePlace (X := X)) :
    ¬ Nonempty (UnitSphereReadoutDonor (X := X) (mu := mu)) := by
  rintro ⟨D⟩
  obtain ⟨v, hv⟩ := h
  have hzero := archimedean_unitSphere_mass_zero (X := X) (mu := mu) v hv
  have hpos : 0 < mu v (unitSphere (X := X) v) := D.mass_pos v
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

/-- Exact actual donor target.  Named sorry: besides the archimedean
obstruction, actual procession weights/dimensions and a positive-finite
nonarchimedean sphere-mass construction are not present in the tree. -/
def UnitSphereReadoutDonorActualTarget : Prop :=
  Nonempty (UnitSphereReadoutDonor (X := X) (mu := mu))

/-- The P6L readout actual target, conditional on the donor. -/
def P6ReadoutActualTarget : Prop :=
  Nonempty (P6Readout (X := X) (mu := mu))

theorem P6ReadoutActualTarget_of_donor
    (h : UnitSphereReadoutDonorActualTarget (X := X) (mu := mu)) :
    P6ReadoutActualTarget (X := X) (mu := mu) := by
  rcases h with ⟨D⟩
  exact ⟨P6Readout.ofUnitSphereDonor (X := X) (mu := mu) D⟩

end LeanFormal.IUT.N8Closure.UnitSphereReadoutDonorActual