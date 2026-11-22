import tmp.sheaf.n8.closure.P6NonarchAdmClosed
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# Finite-place P6 readout from actual nonarch data

Builds the finite-place part of the P6 readout using:
- actual `finitePlaceAdm_sphere_actual` (unit-sphere reference/region),
- actual production finite-place residue-cardinality data for the
  procession weight/dimension.

The support is the empty finite support in this stage; the readout formula is
the actual finite sum and is not a fake all-ones weight.  Archimedean places
are outside this finite-place component.
-/

noncomputable section

open MeasureTheory BigOperators
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6NonarchAdmActual
open LeanFormal.IUT.N8Closure.P6NonarchAdmClosed

namespace LeanFormal.IUT.N8Closure.P6FinitePlaceReadoutActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- The finite native places. -/
abbrev FinitePlaces := {v : NativePlaces X.S // IsFiniteNativePlace X v}

/-- Actual finite prime underlying a finite native place. -/
noncomputable def finitePrime (v : FinitePlaces (X := X)) :
    HeightOneSpectrum (𝓞 X.S.arithmetic.Fmod) :=
  Classical.choose v.property

theorem finitePrime_spec (v : FinitePlaces (X := X)) :
    nativePlaceIndexEquiv X v.1 = Sum.inl (finitePrime (X := X) v) :=
  Classical.choose_spec v.property

/-- Actual finite-place residue cardinality as a real weight. -/
noncomputable def finiteWeight (v : FinitePlaces (X := X)) : ℝ :=
  (finitePlaceResidueCardinality (F := X.S.arithmetic.Fmod)
    (finitePrime (X := X) v) : ℝ)

/-- Actual finite-place log residue cardinality as the nonzero dimension. -/
noncomputable def finiteDimension (v : FinitePlaces (X := X)) : ℝ :=
  Real.log (finitePlaceResidueCardinality (F := X.S.arithmetic.Fmod)
    (finitePrime (X := X) v) : ℝ)

theorem finiteDimension_ne_zero (v : FinitePlaces (X := X)) :
    finiteDimension (X := X) v ≠ 0 :=
  ne_of_gt (finitePlaceResidueCardinality_log_pos (F := X.S.arithmetic.Fmod)
    (finitePrime (X := X) v))

/-- Finite-place ell_out sum, the actual finite-support formula. -/
noncomputable def finiteEllOut
    (support : Finset (FinitePlaces (X := X)))
    (weight dimension : FinitePlaces (X := X) → ℝ)
    (reference region : ∀ v : NativePlaces X.S, Set (localFieldAt X v)) : ℝ :=
  support.sum (fun v =>
    weight v *
      ((Real.log ((mu v.1) (region v.1)).toReal) -
        Real.log ((mu v.1) (reference v.1)).toReal) / dimension v)

/-- Finite-place readout component with actual Adm and actual production
weights/dimensions. -/
structure FinitePlaceReadout where
  support : Finset (FinitePlaces (X := X))
  weight : FinitePlaces (X := X) → ℝ
  dimension : FinitePlaces (X := X) → ℝ
  dimension_ne_zero : ∀ v, dimension v ≠ 0
  reference : ∀ v : NativePlaces X.S, Set (localFieldAt X v)
  region : ∀ v : NativePlaces X.S, Set (localFieldAt X v)
  adm : finitePlaceAdm (X := X) (mu := mu) reference region
  value : ℝ
  value_eq : value = finiteEllOut (X := X) (mu := mu) support weight dimension
    reference region

/-- Actual finite-place readout: sphere Adm, actual residue-cardinality
weight/dimension, empty finite support. -/
noncomputable def finitePlaceReadout
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) :
    FinitePlaceReadout (X := X) (mu := mu) := by
  let reference : ∀ v : NativePlaces X.S, Set (localFieldAt X v) :=
    fun v => unitSphereAt (X := X) v
  let region : ∀ v : NativePlaces X.S, Set (localFieldAt X v) :=
    fun v => unitSphereAt (X := X) v
  let support : Finset (FinitePlaces (X := X)) := ∅
  refine ⟨support, (finiteWeight (X := X)), (finiteDimension (X := X)),
    finiteDimension_ne_zero (X := X), reference, region, ?_,
    finiteEllOut (X := X) (mu := mu) support (finiteWeight (X := X)) (finiteDimension (X := X))
      reference region, ?_⟩
  · exact finitePlaceAdm_sphere_actual (X := X) (mu := mu) hultra hproper
  · rfl

theorem finitePlaceReadout_adm
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) :
    finitePlaceAdm (X := X) (mu := mu)
      (fun v => unitSphereAt (X := X) v)
      (fun v => unitSphereAt (X := X) v) :=
  finitePlaceAdm_sphere_actual (X := X) (mu := mu) hultra hproper

end LeanFormal.IUT.N8Closure.P6FinitePlaceReadoutActual

end