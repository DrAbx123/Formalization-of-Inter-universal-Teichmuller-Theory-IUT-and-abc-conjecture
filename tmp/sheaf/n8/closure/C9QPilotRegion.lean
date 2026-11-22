import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotGlobalNormalization

/-!
# C9 q-pilot region/log-volume interface

Builds the actual q-pilot region from the native C3 q (`NativeC3.nativeQActual`),
the actual production q-pilot Real readout
`ArithmeticQPilotLogVolume.localSignedLog`, and the actual Kummer-relative
unit norm log degree.  The procession-normalized volume has no production
donor; its exact target is stated with a theorem-level named sorry.

Region source is a singleton in the actual completion.  No free Type or free
Real field is introduced.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

namespace LeanFormal.IUT.N8Closure.C9QPilotRegion

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual native C3 q-pilot candidate. -/
abbrev nativeQ : FinitePlaceQCandidate (nativeFPlaceOverBad X) :=
  NativeC3.nativeQActual X

/-- Actual q-pilot region source: the singleton of the native q in the actual
completion. -/
def qPilotRegionSource : Set (Completion (nativeFPlaceOverBad X)) :=
  {(nativeQ X).q}

theorem qPilotRegionSource_nonempty : (qPilotRegionSource X).Nonempty :=
  ⟨(nativeQ X).q, rfl⟩

theorem nativeQ_mem_region : (nativeQ X).q ∈ qPilotRegionSource X := rfl

/-- Actual signed q-pilot Real readout from production ArithmeticQPilotLogVolume. -/
def qPilotSignedLog : ℝ :=
  ArithmeticQPilotLogVolume.localSignedLog (nativeQ X)

/-- Actual q-pilot magnitude. -/
def qPilotLogMagnitude : ℝ :=
  ArithmeticQPilotLogVolume.localLogMagnitude (nativeQ X)

theorem qPilotSignedLog_eq_localSignedLog :
    qPilotSignedLog X = ArithmeticQPilotLogVolume.localSignedLog (nativeQ X) := rfl

theorem qPilotSignedLog_neg : qPilotSignedLog X < 0 :=
  ArithmeticQPilotLogVolume.localSignedLog_neg (nativeQ X)

/-- Actual Kummer-relative q-pilot volume: the unit norm log degree of the
actual q-unit. -/
def qPilotKummerRelativeVolume : ℝ :=
  Multiplicative.toAdd
    (unitNormLogDegree (Completion (nativeFPlaceOverBad X))
      (Units.mk0 (nativeQ X).q (nativeQ X).q_ne_zero))

/-- The Kummer-relative volume is exactly the production signed q log. -/
theorem qPilotKummerRelativeVolume_eq :
    qPilotKummerRelativeVolume X = qPilotSignedLog X :=
  ArithmeticQPilotLogVolume.unitNormLogDegree_q (nativeQ X)

/-- Actual selected singleton for the production arithmetic q-pilot normalization. -/
def qPilotSelectedPlaces : Finset (NumberField.FinitePlace X.S.arithmetic.F) :=
  {nativeFPlaceOverBad X}

theorem qPilotSelectedPlaces_nonempty : (qPilotSelectedPlaces X).Nonempty :=
  ⟨nativeFPlaceOverBad X, by simp [qPilotSelectedPlaces]⟩

/-- Actual parameters on the selected singleton: the native q at the selected
native place. -/
noncomputable def qPilotSelectedParameters
    (p : {x // x ∈ qPilotSelectedPlaces X}) :
    FinitePlaceQCandidate p.val := by
  have hp : p.val = nativeFPlaceOverBad X :=
    Finset.mem_singleton.mp (by simpa [qPilotSelectedPlaces] using p.property)
  exact hp ▸ nativeQ X

/-- The actual production conditional procession-normalized q volume at the
selected native place. -/
def qPilotProcessionNormalizedVolume : ℝ :=
  ArithmeticQPilotGlobalNormalization.selectedLowerSignedLog
    (qPilotSelectedPlaces X) (qPilotSelectedParameters X)

/-- Exact target for the procession-normalized q-pilot log-volume.  No
production donor identifies the full procession-normalized volume with the
actual q scalar; this is the exact missing relation. -/
def qPilotProcessionNormalizedVolumeTarget : Prop :=
  qPilotProcessionNormalizedVolume X = qPilotSignedLog X

/-- The q-pilot region/log-volume interface record: actual region source,
actual signed log, actual Kummer-relative volume, and the exact
procession-normalization target. -/
structure QPilotRegionInterface where
  region : Set (Completion (nativeFPlaceOverBad X))
  region_eq : region = qPilotRegionSource X
  signedLog : ℝ
  signedLog_eq : signedLog = qPilotSignedLog X
  kummerRelativeVolume : ℝ
  kummerRelativeVolume_eq : kummerRelativeVolume = qPilotKummerRelativeVolume X
  processionNormalizedVolume : ℝ
  processionNormalizedVolume_eq :
    processionNormalizedVolume = qPilotProcessionNormalizedVolume X

noncomputable def qPilotRegionInterface : QPilotRegionInterface X where
  region := qPilotRegionSource X
  region_eq := rfl
  signedLog := qPilotSignedLog X
  signedLog_eq := rfl
  kummerRelativeVolume := qPilotKummerRelativeVolume X
  kummerRelativeVolume_eq := rfl
  processionNormalizedVolume := qPilotProcessionNormalizedVolume X
  processionNormalizedVolume_eq := rfl

end LeanFormal.IUT.N8Closure.C9QPilotRegion
