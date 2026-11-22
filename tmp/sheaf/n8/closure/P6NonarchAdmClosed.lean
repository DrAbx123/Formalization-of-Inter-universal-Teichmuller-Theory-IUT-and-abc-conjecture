import tmp.sheaf.n8.closure.P6NonarchAdmActual
import tmp.sheaf.n8.closure.P6NonarchSphereMassActual

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# Finite-place Adm closed from actual sphere mass

Instantiates `P6NonarchSphereMassActual.unitSphere_measure_pos_lt_top` at the
finite native places and closes the finite-place Adm component of
`P6NonarchAdmActual`.  The archimedean branch is left to the log-descent no-go.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6NonarchAdmActual
open LeanFormal.IUT.N8Closure.P6NonarchSphereMassActual

namespace LeanFormal.IUT.N8Closure.P6NonarchAdmClosed

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Actual finite-place mass: each finite native local field is
nonarchimedean and proper, so the unit sphere has positive finite Haar mass. -/
theorem finitePlace_unitSphere_mass_actual
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v))
    (v : NativePlaces X.S) (hv : IsFiniteNativePlace X v) :
    0 < mu v (unitSphereAt (X := X) v) ∧
      mu v (unitSphereAt (X := X) v) < ⊤ := by
  letI : IsUltrametricDist (localFieldAt X v) := hultra v hv
  letI : ProperSpace (localFieldAt X v) := hproper v hv
  have h := unitSphere_measure_pos_lt_top (K := localFieldAt X v) (mu v)
  simpa [unitSphereAt, unitSphere] using h

/-- Actual finite-place Adm from the actual sphere mass; no named mass gap.
  Only the two actual local-field instance facts are hypotheses. -/
theorem finitePlaceAdm_sphere_actual
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) :
    finitePlaceAdm (X := X) (mu := mu)
      (fun v => unitSphereAt (X := X) v)
      (fun v => unitSphereAt (X := X) v) := by
  apply finitePlaceAdm_sphere_of_mass
  · intro v hv
    exact (finitePlace_unitSphere_mass_actual (X := X) (mu := mu)
      hultra hproper v hv).1
  · intro v hv
    exact (finitePlace_unitSphere_mass_actual (X := X) (mu := mu)
      hultra hproper v hv).2

end LeanFormal.IUT.N8Closure.P6NonarchAdmClosed

end
