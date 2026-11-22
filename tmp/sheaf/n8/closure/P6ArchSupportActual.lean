import tmp.sheaf.n8.closure.P6ArchReadoutActual
import tmp.sheaf.n8.closure.P6NativePlacesArchimedeanAudit
import Mathlib

/-!
# Actual nonempty archimedean support

Builds a nonempty finite support for the archimedean readout from an actual
base infinite place (Mathlib complex embedding), the actual native place
bridge, and the actual `InfinitePlace.mult` weight/dimension.  No arbitrary
support or region.
-/

noncomputable section

open MeasureTheory BigOperators Set Metric
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6NonarchAdmActual
open LeanFormal.IUT.N8Closure.P6ArchReadoutActual
open LeanFormal.IUT.N8Closure.P6RelaxedGlobalReadout
open LeanFormal.IUT.N8Closure.P6NativePlacesArchimedeanAudit

namespace LeanFormal.IUT.N8Closure.P6ArchSupportActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Every number field base has an infinite place. -/
theorem baseInfinitePlace_nonempty :
    Nonempty (NumberField.InfinitePlace X.S.arithmetic.Fmod) :=
  inferInstance

noncomputable def baseInfinitePlace : NumberField.InfinitePlace X.S.arithmetic.Fmod :=
  Classical.choice (baseInfinitePlace_nonempty (X := X))

theorem archimedeanNativePlace_not_finite
    (w : NumberField.InfinitePlace X.S.arithmetic.Fmod) :
    ¬ IsFiniteNativePlace (X := X) (archimedeanNativePlace X w) := by
  rintro ⟨p, hp⟩
  have hindex : nativePlaceIndexEquiv X (archimedeanNativePlace X w) = Sum.inr w := by
    simp [nativePlaceIndexEquiv, archimedeanNativePlace, NativeInput.nativePlaceEquiv,
      placeIndexEquiv]
    rfl
  rw [hindex] at hp
  cases hp

/-- Actual nonempty archimedean place from the base infinite place. -/
noncomputable def archActualPlace : ArchimedeanPlaces (X := X) :=
  ⟨archimedeanNativePlace X (baseInfinitePlace X),
    archimedeanNativePlace_not_finite X (baseInfinitePlace X)⟩

/-- Actual singleton finite support for the archimedean readout. -/
def archSupportActual : Finset (ArchimedeanPlaces (X := X)) :=
  {archActualPlace X}

theorem archSupportActual_nonempty : (archSupportActual X).Nonempty :=
  ⟨archActualPlace X, by simp [archSupportActual]⟩

/-- Actual archimedean readout with nonempty support, actual weights/dimensions,
and actual closed-ball region. -/
noncomputable def archReadoutNonempty
    (hproperArch : ∀ v : ArchimedeanPlaces (X := X),
      ProperSpace (localFieldAt X v.1)) :
    ArchReadout (X := X) (mu := mu) where
  support := archSupportActual X
  weight := archWeight (X := X)
  dimension := archDimension (X := X)
  dimension_ne_zero := archDimension_ne_zero (X := X)
  adm := archAdm_closedBall (X := X) (mu := mu) hproperArch
  value := archEllOut (X := X) (mu := mu) (archSupportActual X)

theorem archReadoutNonempty_support
    (hproperArch : ∀ v : ArchimedeanPlaces (X := X),
      ProperSpace (localFieldAt X v.1)) :
    (archReadoutNonempty (X := X) (mu := mu) hproperArch).support.Nonempty :=
  archSupportActual_nonempty X

/-- Actual nonempty-support ArchReadout exists. -/
theorem archReadoutNonempty_exists
    (hproperArch : ∀ v : ArchimedeanPlaces (X := X),
      ProperSpace (localFieldAt X v.1)) :
    Nonempty (ArchReadout (X := X) (mu := mu)) :=
  ⟨archReadoutNonempty (X := X) (mu := mu) hproperArch⟩

end LeanFormal.IUT.N8Closure.P6ArchSupportActual
