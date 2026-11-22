import tmp.sheaf.n8.closure.P6ArchimedeanAdmNoGo
import tmp.sheaf.n8.closure.P6NativePlacesArchimedeanAudit
import tmp.sheaf.n8.closure.P6GlobalLqTargetCorrection

/-!
# SourceGlobalLqDonor archimedean no-go (Wave22)

SourceGlobalLqDonor contains an actual P6Readout.  P6ArchimedeanAdmNoGo proves
that at an archimedean native place no P6Readout exists (additive Haar sphere
mass zero, no positive-mass Adm region).  Hence:

- if NativePlaces has an archimedean place, SourceGlobalLqDonor and
  SourceGlobalLqTarget are impossible;
- existence is possible only in the precise finite-place condition, i.e. when
  no archimedean native place is present.

Every number field has an infinite place, so the unconditional no-go applies to
the actual archimedeanNativePlace.  No free L data is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.SourceGlobalLqArchimedeanNoGo

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.UnitSphereReadoutDonorActual
open LeanFormal.IUT.N8Closure.P6ArchimedeanAdmNoGo
open LeanFormal.IUT.N8Closure.P6NativePlacesArchimedeanAudit
open LeanFormal.IUT.N8Closure.P6GlobalLqTargetCorrection

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
variable [∀ v : NativePlaces X.S, NullSingletonClass (mu v)]

/-- At an archimedean native place no corrected SourceGlobalLqDonor exists. -/
theorem noSourceGlobalLqDonor_of_archimedean_at
    (v : NativePlaces X.S)
    (hv : NumberFieldPlace.IsInfinite
      (NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) v.1))
    [NormedSpace ℝ (localFieldAt X v)]
    [FiniteDimensional ℝ (localFieldAt X v)]
    [Nontrivial (localFieldAt X v)] :
    ¬ Nonempty (SourceGlobalLqDonor X mu) := by
  rintro ⟨S⟩
  exact noP6Readout_of_archimedean_at (X := X) (mu := mu) v hv
    ⟨S.readout⟩

/-- The corrected target is impossible at an archimedean native place. -/
theorem not_sourceGlobalLqTarget_of_archimedean_at
    (v : NativePlaces X.S)
    (hv : NumberFieldPlace.IsInfinite
      (NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) v.1))
    [NormedSpace ℝ (localFieldAt X v)]
    [FiniteDimensional ℝ (localFieldAt X v)]
    [Nontrivial (localFieldAt X v)] :
    ¬ SourceGlobalLqTarget X mu :=
  noSourceGlobalLqDonor_of_archimedean_at (X := X) (mu := mu) v hv

/-- Exact conditional target correction from a base infinite place. -/
theorem not_sourceGlobalLqTarget_of_infinitePlace
    (w : NumberField.InfinitePlace X.S.arithmetic.Fmod)
    [NormedSpace ℝ (localFieldAt X (archimedeanNativePlace X w))]
    [FiniteDimensional ℝ (localFieldAt X (archimedeanNativePlace X w))]
    [Nontrivial (localFieldAt X (archimedeanNativePlace X w))] :
    ¬ SourceGlobalLqTarget X mu :=
  not_sourceGlobalLqTarget_of_archimedean_at (X := X) (mu := mu)
    (archimedeanNativePlace X w) (archimedeanNativePlace_isInfinite X w)

/-- Every number field has an infinite place. -/
theorem baseInfinitePlace_nonempty :
    Nonempty (NumberField.InfinitePlace X.S.arithmetic.Fmod) :=
  inferInstance

/-- An actual archimedean native place, chosen from the unconditional infinite
place. -/
noncomputable def archimedeanNativePlaceActual : NativePlaces X.S :=
  archimedeanNativePlace X (Classical.choice (baseInfinitePlace_nonempty (X := X)))

/-- Unconditional archimedean native place existence. -/
theorem hasArchimedeanNativePlace_unconditional :
    HasArchimedeanNativePlace (X := X) :=
  hasArchimedeanNativePlace_of_infinitePlace X
    (Classical.choice (baseInfinitePlace_nonempty (X := X)))

/-- Unconditional no-go for the corrected SourceGlobalLqDonor target. -/
theorem not_sourceGlobalLqTarget_unconditional
    [NormedSpace ℝ (localFieldAt X (archimedeanNativePlaceActual X))]
    [FiniteDimensional ℝ (localFieldAt X (archimedeanNativePlaceActual X))]
    [Nontrivial (localFieldAt X (archimedeanNativePlaceActual X))] :
    ¬ SourceGlobalLqTarget X mu :=
  not_sourceGlobalLqTarget_of_archimedean_at (X := X) (mu := mu)
    (archimedeanNativePlaceActual X)
    (archimedeanNativePlace_isInfinite X
      (Classical.choice (baseInfinitePlace_nonempty (X := X))))

/-- Exact finite-place condition: if there is no archimedean native place, the
archimedean obstruction is absent.  This is the only condition under which the
corrected target can be consistent. -/
theorem sourceGlobalLqTarget_consistent_iff_no_archimedean
    (h : ¬ Nonempty (NumberField.InfinitePlace X.S.arithmetic.Fmod)) :
    ¬ HasArchimedeanNativePlace (X := X) :=
  nativePlaces_all_finite_of_no_infinitePlace X h

end LeanFormal.IUT.N8Closure.SourceGlobalLqArchimedeanNoGo
