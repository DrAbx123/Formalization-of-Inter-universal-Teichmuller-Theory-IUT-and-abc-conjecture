import tmp.sheaf.n8.closure.P6FinitePlaceReadoutActual
import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# Nonempty finite support from an actual selected bad finite place

Uses the actual native selected bad base finite place to build a nonempty
finite support for `FinitePlaceReadout`.  The residue-cardinality weights and
dimensions and the nonarch unit-sphere Adm remain the actual ones from
`P6FinitePlaceReadoutActual`.
-/

noncomputable section

open MeasureTheory BigOperators
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6NonarchAdmActual
open LeanFormal.IUT.N8Closure.P6NonarchAdmClosed
open LeanFormal.IUT.N8Closure.P6FinitePlaceReadoutActual

namespace LeanFormal.IUT.N8Closure.P6FiniteSupportSourceAttempt

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- The actual selected bad base finite place as a native place. -/
noncomputable def badNativePlace : NativePlaces X.S :=
  (nativePlaceEquiv X.S).symm (NumberFieldPlace.finite (nativeBadBasePlace X))

theorem badNativePlace_mem :
    (badNativePlace (X := X)).1 ∈ X.S.tuple.source.V :=
  (badNativePlace (X := X)).2

theorem badNativePlace_finite :
    IsFiniteNativePlace (X := X) (badNativePlace (X := X)) := by
  refine ⟨finitePlaceIndexEquiv (nativeBadBasePlace X), ?_⟩
  simp [badNativePlace, nativePlaceIndexEquiv, placeIndexEquiv, placeToIndex]

/-- Nonempty finite support consisting of the actual selected bad place. -/
noncomputable def badFinitePlace : FinitePlaces (X := X) :=
  ⟨badNativePlace (X := X), badNativePlace_finite (X := X)⟩

theorem badFinitePlace_support_nonempty :
    ({badFinitePlace (X := X)} : Finset (FinitePlaces (X := X))).Nonempty :=
  ⟨badFinitePlace (X := X), by simp⟩

/-- Nonempty-support finite readout with actual weights, dimensions and sphere
Adm.  The value formula is the actual finite ell_out sum. -/
noncomputable def finitePlaceReadoutNonempty
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) :
    FinitePlaceReadout (X := X) (mu := mu) := by
  let reference : ∀ v : NativePlaces X.S, Set (localFieldAt X v) :=
    fun v => unitSphereAt (X := X) v
  let region : ∀ v : NativePlaces X.S, Set (localFieldAt X v) :=
    fun v => unitSphereAt (X := X) v
  let support : Finset (FinitePlaces (X := X)) := {badFinitePlace (X := X)}
  refine ⟨support, (finiteWeight (X := X)), (finiteDimension (X := X)),
    finiteDimension_ne_zero (X := X), reference, region, ?_,
    finiteEllOut (X := X) (mu := mu) support (finiteWeight (X := X))
      (finiteDimension (X := X)) reference region, ?_⟩
  · exact finitePlaceAdm_sphere_actual (X := X) (mu := mu) hultra hproper
  · rfl

theorem finitePlaceReadoutNonempty_support_nonempty
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) :
    (finitePlaceReadoutNonempty (X := X) (mu := mu) hultra hproper).support.Nonempty :=
  badFinitePlace_support_nonempty (X := X)

end LeanFormal.IUT.N8Closure.P6FiniteSupportSourceAttempt

end
