import tmp.sheaf.xif.paper.WeakThetaHullLogVolumeActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual

/-! # Positive Theta-hull magnitude versus the signed q-pilot scalar

The paper signed comparison is

  qSigned <= -positiveThetaHull,

where qSigned = nativeGlobalQPilotNormalizedSignedLogVolume = -Q and
positiveThetaHull = |log Theta| is the positive Theta-hull magnitude.  This is
the direct -T >= -Q direction, not a comparison of a signed log-volume with a
positive magnitude and not a zero-volume/trivial case.

The actual Theta-hull log-volume of WeakThetaHullLogVolumeActual is a Haar
log-volume whose sign is not assumed; its positive magnitude is its absolute
value.  The actual q-pilot scalar is the native normalized signed log-volume.
The comparison is stated and reduced exactly; it is not asserted.

No fake inequality, zero volume, carrier equivalence, sorry, axiom, True, or
PUnit is used. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PositiveHullVsQPilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.WeakThetaHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual positive Theta-hull magnitude |log Theta|, from the actual weak
C3 log-shell tensor Haar log-volume. -/
noncomputable def positiveThetaHullLogVolume : Real :=
  |weakThetaHullLogVolume (I := I) C3|

theorem positiveThetaHullLogVolume_nonneg :
    0 <= positiveThetaHullLogVolume (I := I) C3 :=
  abs_nonneg _

/-- The actual signed q-pilot scalar qSigned = -Q. -/
noncomputable def qPilotSignedScalar : Real :=
  nativeGlobalQPilotNormalizedSignedLogVolume T

/-- The actual q-pilot magnitude Q. -/
noncomputable def qPilotMagnitude : Real :=
  nativeGlobalQPilotNormalizedLogMagnitude T

theorem qPilotSignedScalar_eq_neg :
    qPilotSignedScalar T = -qPilotMagnitude T := rfl

/-- Correct signed comparison: qSigned <= -positiveThetaHull. -/
def PositiveHullVsQPilot : Prop :=
  qPilotSignedScalar T <= -positiveThetaHullLogVolume (I := I) C3

/-- The signed comparison is exactly the positive-magnitude inequality
positiveThetaHull <= Q. -/
theorem positiveHullVsQPilot_iff_magnitude :
    PositiveHullVsQPilot (C3 := C3) T ↔
      positiveThetaHullLogVolume (I := I) C3 <= qPilotMagnitude T := by
  unfold PositiveHullVsQPilot qPilotSignedScalar qPilotMagnitude
    nativeGlobalQPilotNormalizedSignedLogVolume
  constructor <;> intro h <;> linarith

/-- Exact numeric failure condition Q < positiveThetaHull. -/
def PositiveHullVsQPilotObstacle : Prop :=
  qPilotMagnitude T < positiveThetaHullLogVolume (I := I) C3

/-- The signed comparison holds exactly when the numeric obstacle fails. -/
theorem positiveHullVsQPilot_iff_not_obstacle :
    PositiveHullVsQPilot (C3 := C3) T ↔
      ¬ PositiveHullVsQPilotObstacle (C3 := C3) T := by
  rw [positiveHullVsQPilot_iff_magnitude]
  unfold PositiveHullVsQPilotObstacle
  constructor
  · intro h
    exact not_lt_of_ge h
  · intro h
    exact le_of_not_gt h

/-- The numeric obstacle refutes the signed comparison. -/
theorem not_positiveHullVsQPilot_of_obstacle
    (h : PositiveHullVsQPilotObstacle (C3 := C3) T) :
    ¬ PositiveHullVsQPilot (C3 := C3) T := by
  intro hc
  exact (positiveHullVsQPilot_iff_not_obstacle (C3 := C3) T).mp hc h

/-- Exact sign compatibility: if the weak Haar log-volume is nonpositive, the
positive magnitude is exactly its negative (the paper -T reading). -/
def WeakHullNonpositive : Prop :=
  weakThetaHullLogVolume (I := I) C3 <= 0

theorem positiveThetaHull_eq_neg_of_nonpositive
    (h : WeakHullNonpositive (C3 := C3)) :
    positiveThetaHullLogVolume (C3 := C3) =
      -weakThetaHullLogVolume (I := I) C3 := by
  unfold positiveThetaHullLogVolume
  rw [abs_of_nonpos h]

end LeanFormal.IUT.XiFPaper.PositiveHullVsQPilotActual

end
