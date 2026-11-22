import tmp.sheaf.n8.closure.P6NativePlacesArchimedeanAudit
import tmp.sheaf.n8.closure.P6ArchimedeanAdmNoGo
import Mathlib

/-!
# P6 no readout: unconditional archimedean-place existence

Every number field has a complex embedding, hence an infinite place, so
NativePlaces contains an archimedean native place.  This file derives
HasArchimedeanNativePlace X unconditionally and the Wave18 no-Adm/no-P6Readout.
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
open LeanFormal.IUT.N8Closure.P6NativePlacesArchimedeanAudit
open LeanFormal.IUT.N8Closure.P6ArchimedeanAdmNoGo
open LeanFormal.IUT.IUTII.Frobenioid.Example36

namespace LeanFormal.IUT.N8Closure.P6NoReadoutUnconditional

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
variable [∀ v : NativePlaces X.S, NullSingletonClass (mu v)]

theorem baseInfinitePlace_nonempty :
    Nonempty (NumberField.InfinitePlace X.S.arithmetic.Fmod) :=
  inferInstance

noncomputable def baseInfinitePlace : NumberField.InfinitePlace X.S.arithmetic.Fmod :=
  Classical.choice (baseInfinitePlace_nonempty (X := X))

noncomputable def archimedeanNativePlaceActual : NativePlaces X.S :=
  archimedeanNativePlace X (baseInfinitePlace X)

theorem hasArchimedeanNativePlace_unconditional :
    HasArchimedeanNativePlace (X := X) :=
  hasArchimedeanNativePlace_of_infinitePlace X (baseInfinitePlace X)

theorem archimedeanNativePlaceActual_isInfinite :
    NumberFieldPlace.IsInfinite
      (NumberFieldPlace.comap (k := X.S.arithmetic.Fmod)
        (archimedeanNativePlaceActual X).1) :=
  archimedeanNativePlace_isInfinite X (baseInfinitePlace X)

theorem noAdm_unconditional
    [NormedSpace ℝ (localFieldAt X (archimedeanNativePlaceActual X))]
    [FiniteDimensional ℝ (localFieldAt X (archimedeanNativePlaceActual X))]
    [Nontrivial (localFieldAt X (archimedeanNativePlaceActual X))] :
    ¬ ∃ (reference region : GlobalRegion X),
      Adm (X := X) (mu := mu) reference region :=
  noAdm_of_archimedean_at (X := X) (mu := mu)
    (archimedeanNativePlaceActual X) (archimedeanNativePlaceActual_isInfinite X)

theorem noP6Readout_unconditional
    [NormedSpace ℝ (localFieldAt X (archimedeanNativePlaceActual X))]
    [FiniteDimensional ℝ (localFieldAt X (archimedeanNativePlaceActual X))]
    [Nontrivial (localFieldAt X (archimedeanNativePlaceActual X))] :
    ¬ Nonempty (P6Readout (X := X) (mu := mu)) :=
  noP6Readout_of_archimedean_at (X := X) (mu := mu)
    (archimedeanNativePlaceActual X) (archimedeanNativePlaceActual_isInfinite X)

end LeanFormal.IUT.N8Closure.P6NoReadoutUnconditional
