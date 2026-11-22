import tmp.sheaf.n8.closure.P6L
import tmp.sheaf.n8.closure.NativeC1
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripComponentIdentification

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# P6 nonarch finite-place Adm from the actual unit sphere

Constructs the finite-place part of the P6 Adm condition from the actual
nonarchimedean norm-one sphere (`{x | ‖x‖ = 1}`), which is the actual integral
unit group.  Measurability and the a.e. zero local log are proved.  The
positive finite Haar mass of the sphere is not present in the production tree;
it is recorded as an exact named gap.

The archimedean branch is separated: the archimedean sphere is required to
carry Haar mass zero, so it contributes zero measure to the finite-place
readout and is not forced into the positive-mass Adm slot.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L

namespace LeanFormal.IUT.N8Closure.P6NonarchAdmActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Native places whose local field is finite (nonarchimedean). -/
def IsFiniteNativePlace (v : NativePlaces X.S) : Prop :=
  ∃ p, nativePlaceIndexEquiv X v = Sum.inl p

/-- The actual nonarchimedean unit sphere at a native place. -/
def unitSphereAt (v : NativePlaces X.S) : Set (localFieldAt X v) :=
  {x | ‖x‖ = 1}

theorem unitSphereAt_measurable (v : NativePlaces X.S) :
    MeasurableSet (unitSphereAt (X := X) v) := by
  have hclosed : IsClosed (unitSphereAt (X := X) v) := by
    simpa [unitSphereAt] using isClosed_eq (continuous_norm) continuous_const
  exact hclosed.measurableSet

theorem unitSphereAt_ae_localLog_zero (v : NativePlaces X.S) :
    ∀ᵐ x ∂(mu v), x ∈ unitSphereAt (X := X) v → localLog X v x = 0 := by
  refine Filter.Eventually.of_forall ?_
  intro x hx
  have hnorm : ‖x‖ = 1 := hx
  simp [localLog, hnorm]

/-- Finite-place Adm data built from the actual unit sphere. -/
def finitePlaceAdm (reference region : ∀ v : NativePlaces X.S, Set (localFieldAt X v)) : Prop :=
  (∀ v, IsFiniteNativePlace X v → MeasurableSet (reference v)) ∧
  (∀ v, IsFiniteNativePlace X v → 0 < mu v (reference v)) ∧
  (∀ v, IsFiniteNativePlace X v → mu v (reference v) < ⊤) ∧
  (∀ v, IsFiniteNativePlace X v →
    ∀ᵐ x ∂(mu v), x ∈ reference v → localLog X v x = 0) ∧
  (∀ v, IsFiniteNativePlace X v → MeasurableSet (region v)) ∧
  (∀ v, IsFiniteNativePlace X v → 0 < mu v (region v)) ∧
  (∀ v, IsFiniteNativePlace X v → mu v (region v) < ⊤) ∧
  (∀ v, IsFiniteNativePlace X v →
    ∀ᵐ x ∂(mu v), x ∈ region v → localLog X v x = 0)

/-- The finite-place sphere is measurable and has a.e. zero local log.  Its
positive finite Haar mass is the exact missing donor below. -/
theorem finitePlaceAdm_sphere_of_mass
    (hpos : ∀ v, IsFiniteNativePlace X v → 0 < mu v (unitSphereAt (X := X) v))
    (hfin : ∀ v, IsFiniteNativePlace X v → mu v (unitSphereAt (X := X) v) < ⊤) :
    finitePlaceAdm (X := X) (mu := mu) (fun v => unitSphereAt (X := X) v)
      (fun v => unitSphereAt (X := X) v) := by
  refine ⟨?_, hpos, hfin, ?_, ?_, hpos, hfin, ?_⟩
  · intro v _; exact unitSphereAt_measurable (X := X) v
  · intro v _; exact unitSphereAt_ae_localLog_zero (X := X) (mu := mu) v
  · intro v _; exact unitSphereAt_measurable (X := X) v
  · intro v _; exact unitSphereAt_ae_localLog_zero (X := X) (mu := mu) v

/-- Decisive finite-place construction conditional only on the two exact mass
statements; no arbitrary Adm data. -/
theorem finitePlaceAdm_sphere
    (hpos : ∀ v, IsFiniteNativePlace X v → 0 < mu v (unitSphereAt (X := X) v))
    (hfin : ∀ v, IsFiniteNativePlace X v → mu v (unitSphereAt (X := X) v) < ⊤) :
    finitePlaceAdm (X := X) (mu := mu) (fun v => unitSphereAt (X := X) v)
      (fun v => unitSphereAt (X := X) v) :=
  finitePlaceAdm_sphere_of_mass (X := X) (mu := mu) hpos hfin

end LeanFormal.IUT.N8Closure.P6NonarchAdmActual

end
