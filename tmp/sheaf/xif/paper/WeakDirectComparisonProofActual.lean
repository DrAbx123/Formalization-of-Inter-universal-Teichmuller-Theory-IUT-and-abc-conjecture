import tmp.sheaf.xif.paper.WeakThetaHullLogVolumeActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual

/-! # Weak direct Theta-hull / q-pilot inequality: actual quantities and condition

The weak Theta hull log-volume of WeakThetaHullLogVolumeActual is the actual
C3 log-shell tensor Haar log-volume.  The native global q-pilot normalized
signed log-volume of NativeGlobalQPilotNormalizedLogVolumeActual is the actual
sum over V_bad of the local normalized weights times the base q log
magnitudes.

This file states the weak direct comparison

  weakThetaHullLogVolume <= nativeGlobalQPilotNormalizedLogMagnitude,

proves its exact numeric form, and records the exact failure condition.  It
does not assert the inequality, because the C3 tensor Haar log-volume and the
native q-pilot normalized sum are independent actual quantities with no source
theorem relating their numerical values.

No fake inequality, equality, carrier equivalence, sorry, axiom, True, or
PUnit is used. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.WeakDirectComparisonProofActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.WeakThetaHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The weak direct comparison |log Theta|_weak <= |log q|_normalized. -/
def WeakDirectComparison : Prop :=
  weakThetaHullLogVolume (I := I) C3 <=
    nativeGlobalQPilotNormalizedLogMagnitude T

/-- Exact numeric form of the weak comparison. -/
theorem weakDirectComparison_iff_numeric :
    WeakDirectComparison (C3 := C3) T ↔
      weakThetaHullLogVolume (I := I) C3 <=
        ∑ b : Bad (nativePlaceSelection T),
          nativeBadLocalWeight T b * baseQLogMagnitude T b := by
  unfold WeakDirectComparison
  rw [nativeGlobalQPilotNormalizedLogMagnitude_eq]

/-- Exact failure condition of the weak direct comparison. -/
def WeakDirectComparisonObstacle : Prop :=
  ∑ b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b * baseQLogMagnitude T b <
    weakThetaHullLogVolume (I := I) C3

/-- The weak comparison is equivalent to the negation of its exact failure
condition. -/
theorem weakDirectComparison_iff_not_obstacle :
    WeakDirectComparison (C3 := C3) T ↔
      ¬ WeakDirectComparisonObstacle (C3 := C3) T := by
  rw [weakDirectComparison_iff_numeric]
  unfold WeakDirectComparisonObstacle
  constructor
  · intro h
    exact not_lt_of_ge h
  · intro h
    exact le_of_not_gt h

/-- The exact obstruction refutes the weak direct comparison. -/
theorem not_weakDirectComparison_of_obstacle
    (h : WeakDirectComparisonObstacle (C3 := C3) T) :
    ¬ WeakDirectComparison (C3 := C3) T := by
  intro hc
  exact (weakDirectComparison_iff_not_obstacle (C3 := C3) T).mp hc h

