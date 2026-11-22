import tmp.sheaf.n8.closure.UnitSphereReadoutDonorActual
import Mathlib

/-!
# P6 archimedean Adm no-go

Target correction: at an archimedean native place the additive Haar mass of the
norm-one unit sphere is zero (Mathlib `addHaar_sphere`), hence the set where the
local log vanishes has measure zero, so no P6 Adm region with positive mass and
a.e. zero local log can exist.  Consequently no P6Readout exists when an
archimedean native place is present.  No old L0.5 target or arbitrary data.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6ReadoutUnitSphereAttempt
open LeanFormal.IUT.N8Closure.UnitSphereReadoutDonorActual

namespace LeanFormal.IUT.N8Closure.P6ArchimedeanAdmNoGo

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
variable [∀ v : NativePlaces X.S, NullSingletonClass (mu v)]

/-- At an archimedean native place the additive Haar mass of the unit sphere is zero. -/
theorem archimedean_unitSphere_mass_zero_mathlib
    (v : NativePlaces X.S)
    (hv : NumberFieldPlace.IsInfinite
      (NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) v.1))
    [NormedSpace ℝ (localFieldAt X v)] [FiniteDimensional ℝ (localFieldAt X v)]
    [Nontrivial (localFieldAt X v)] :
    mu v (unitSphere (X := X) v) = 0 := by
  have hsphere : unitSphere (X := X) v =
      Metric.sphere (0 : localFieldAt X v) (1 : ℝ) := by
    ext x
    simp [unitSphere, Metric.sphere, dist_eq_norm]
  rw [hsphere]
  exact MeasureTheory.Measure.addHaar_sphere (mu v) 0 1

/-- The local-log-zero set has measure zero at an archimedean place. -/
theorem localLog_zero_measure_zero_of_sphere_zero
    (v : NativePlaces X.S)
    (hsphere : mu v (unitSphere (X := X) v) = 0) :
    mu v {x : localFieldAt X v | localLog (X := X) v x = 0} = 0 := by
  have hsubset : {x : localFieldAt X v | localLog (X := X) v x = 0} ⊆ unitSphere (X := X) v ∪ ({0} : Set (localFieldAt X v)) := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inr hx0
    · left
      have hnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hnorm : ‖x‖ = 1 := Real.eq_one_of_pos_of_log_eq_zero hnorm_pos hx
      simpa [unitSphere] using hnorm
  have hzero : mu v (unitSphere (X := X) v ∪ ({0} : Set (localFieldAt X v))) = 0 := by
    rw [measure_union_null_iff]
    exact ⟨hsphere, measure_singleton 0⟩
  exact measure_mono_null hsubset hzero

/-- No positive-mass region can be a.e. supported on the local-log-zero set at an archimedean place. -/
theorem no_pos_ae_localLog_zero_of_sphere_zero
    (v : NativePlaces X.S)
    (hsphere : mu v (unitSphere (X := X) v) = 0)
    {region : Set (localFieldAt X v)}
    (hpos : 0 < mu v region)
    (hae : ∀ᵐ x ∂(mu v), x ∈ region → localLog (X := X) v x = 0) :
    False := by
  have hsub : region ≤ᵐ[mu v] {x : localFieldAt X v | localLog (X := X) v x = 0} := hae
  have hle : mu v region ≤ mu v {x : localFieldAt X v | localLog (X := X) v x = 0} := measure_mono_ae hsub
  have hzero := localLog_zero_measure_zero_of_sphere_zero (X := X) (mu := mu) v hsphere
  rw [hzero] at hle
  exact not_lt_of_ge hle hpos

/-- No admissible global reference/region pair exists at an archimedean native place. -/
theorem noAdm_of_archimedean_at
    (v : NativePlaces X.S)
    (hv : NumberFieldPlace.IsInfinite
      (NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) v.1))
    [NormedSpace ℝ (localFieldAt X v)] [FiniteDimensional ℝ (localFieldAt X v)]
    [Nontrivial (localFieldAt X v)] :
    ¬ ∃ (reference region : GlobalRegion X),
      Adm (X := X) (mu := mu) reference region := by
  rintro ⟨reference, region, hadm⟩
  have hsphere := archimedean_unitSphere_mass_zero_mathlib (X := X) (mu := mu) v hv
  rcases hadm with ⟨hmr, hpr, hfr, haer, hmreg, hpr2, hfr2, haereg⟩
  exact no_pos_ae_localLog_zero_of_sphere_zero (X := X) (mu := mu) v hsphere
    (hpr v) (haer v)

/-- No P6Readout exists at an archimedean native place. -/
theorem noP6Readout_of_archimedean_at
    (v : NativePlaces X.S)
    (hv : NumberFieldPlace.IsInfinite
      (NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) v.1))
    [NormedSpace ℝ (localFieldAt X v)] [FiniteDimensional ℝ (localFieldAt X v)]
    [Nontrivial (localFieldAt X v)] :
    ¬ Nonempty (P6Readout (X := X) (mu := mu)) := by
  rintro ⟨R⟩
  exact noAdm_of_archimedean_at (X := X) (mu := mu) v hv
    ⟨R.reference, R.region, R.adm⟩
end LeanFormal.IUT.N8Closure.P6ArchimedeanAdmNoGo
