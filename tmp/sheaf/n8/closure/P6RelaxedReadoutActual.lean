import tmp.sheaf.n8.closure.P6FiniteSupportSourceAttempt
import tmp.sheaf.n8.closure.P6NonarchAdmClosed

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# Relaxed finite-place P6 readout

The old frozen `P6L.Adm` requires an almost-everywhere zero local log on
positive-mass reference and region.  On the actual nonarch unit sphere this is
fine, but the frozen global condition must hold at every native place including
archimedean ones; the archimedean unit sphere has mass zero, so it cannot be
the positive-mass reference of the frozen Adm.  That frozen target is archived.

This file uses the corrected reference-relative relaxed Adm: measurability plus
positive finite Haar mass.  On finite places the actual nonarch unit sphere
supplies both, so the relaxed readout is constructed without arbitrary weights
or regions.
-/

noncomputable section

open MeasureTheory BigOperators
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6NonarchAdmActual
open LeanFormal.IUT.N8Closure.P6NonarchAdmClosed
open LeanFormal.IUT.N8Closure.P6FinitePlaceReadoutActual
open LeanFormal.IUT.N8Closure.P6FiniteSupportSourceAttempt

namespace LeanFormal.IUT.N8Closure.P6RelaxedReadoutActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Relaxed Adm on the finite native places: only measurability and positive
finite Haar mass, reference-relative; no a.e. zero local log. -/
def RelaxedAdmFinite
    (reference region : (v : FinitePlaces (X := X)) →
      Set (localFieldAt X v.1)) : Prop :=
  (∀ v, MeasurableSet (reference v)) ∧
  (∀ v, 0 < mu v.1 (reference v)) ∧
  (∀ v, mu v.1 (reference v) < ⊤) ∧
  (∀ v, MeasurableSet (region v)) ∧
  (∀ v, 0 < mu v.1 (region v)) ∧
  (∀ v, mu v.1 (region v) < ⊤)

/-- Actual relaxed Adm for the nonarch unit sphere. -/
theorem relaxedAdmFinite_sphere
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) :
    RelaxedAdmFinite (X := X) (mu := mu)
      (fun v => unitSphereAt (X := X) v.1)
      (fun v => unitSphereAt (X := X) v.1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v; exact unitSphereAt_measurable (X := X) v.1
  · intro v
    exact (finitePlace_unitSphere_mass_actual (X := X) (mu := mu)
      hultra hproper v.1 v.2).1
  · intro v
    exact (finitePlace_unitSphere_mass_actual (X := X) (mu := mu)
      hultra hproper v.1 v.2).2
  · intro v; exact unitSphereAt_measurable (X := X) v.1
  · intro v
    exact (finitePlace_unitSphere_mass_actual (X := X) (mu := mu)
      hultra hproper v.1 v.2).1
  · intro v
    exact (finitePlace_unitSphere_mass_actual (X := X) (mu := mu)
      hultra hproper v.1 v.2).2

/-- Relaxed finite-place ell_out formula. -/
noncomputable def relaxedFiniteEllOut
    (support : Finset (FinitePlaces (X := X)))
    (weight dimension : FinitePlaces (X := X) → ℝ)
    (reference region : (v : FinitePlaces (X := X)) →
      Set (localFieldAt X v.1)) : ℝ :=
  support.sum (fun v =>
    weight v *
      ((Real.log ((mu v.1) (region v)).toReal) -
        Real.log ((mu v.1) (reference v)).toReal) / dimension v)

/-- Corrected relaxed finite-place readout. -/
structure RelaxedFiniteReadout where
  support : Finset (FinitePlaces (X := X))
  weight : FinitePlaces (X := X) → ℝ
  dimension : FinitePlaces (X := X) → ℝ
  dimension_ne_zero : ∀ v, dimension v ≠ 0
  reference : (v : FinitePlaces (X := X)) → Set (localFieldAt X v.1)
  region : (v : FinitePlaces (X := X)) → Set (localFieldAt X v.1)
  adm : RelaxedAdmFinite (X := X) (mu := mu) reference region
  value : ℝ
  value_eq : value = relaxedFiniteEllOut (X := X) (mu := mu) support weight
    dimension reference region

/-- Actual nonempty-support relaxed readout from the selected bad finite place
and the actual nonarch unit sphere. -/
noncomputable def relaxedFiniteReadout
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) :
    RelaxedFiniteReadout (X := X) (mu := mu) := by
  let reference : (v : FinitePlaces (X := X)) → Set (localFieldAt X v.1) :=
    fun v => unitSphereAt (X := X) v.1
  let region : (v : FinitePlaces (X := X)) → Set (localFieldAt X v.1) :=
    fun v => unitSphereAt (X := X) v.1
  let support : Finset (FinitePlaces (X := X)) := {badFinitePlace (X := X)}
  refine ⟨support, (finiteWeight (X := X)), (finiteDimension (X := X)),
    finiteDimension_ne_zero (X := X), reference, region, ?_,
    relaxedFiniteEllOut (X := X) (mu := mu) support (finiteWeight (X := X))
      (finiteDimension (X := X)) reference region, rfl⟩
  exact relaxedAdmFinite_sphere (X := X) (mu := mu) hultra hproper

theorem relaxedFiniteReadout_adm
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) :
    RelaxedAdmFinite (X := X) (mu := mu)
      (fun v => unitSphereAt (X := X) v.1)
      (fun v => unitSphereAt (X := X) v.1) :=
  relaxedAdmFinite_sphere (X := X) (mu := mu) hultra hproper

theorem relaxedFiniteReadout_support_nonempty
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) :
    (relaxedFiniteReadout (X := X) (mu := mu) hultra hproper).support.Nonempty :=
  badFinitePlace_support_nonempty (X := X)

end LeanFormal.IUT.N8Closure.P6RelaxedReadoutActual

end
