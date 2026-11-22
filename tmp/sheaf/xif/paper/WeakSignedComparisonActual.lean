import tmp.sheaf.xif.paper.WeakDirectComparisonProofActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual

/-! # Correct weak signed comparison: -|log Theta| >= -|log q|

The paper quantity is

  -|log Theta| >= -|log q|,

i.e. the negative Theta magnitude is at least the negative q magnitude,
equivalently |log Theta| <= |log q| (T <= Q).  It is not a comparison of a
signed log-volume with a positive magnitude.

The actual weakThetaHullLogVolume is an actual Haar log-volume
(actualC3LogShellTensorLogVolume); its sign is not proved nonnegative, so its
paper magnitude is the absolute value

  weakThetaHullMagnitude = |weakThetaHullLogVolume|.

This file constructs the correct signed comparison

  nativeGlobalQPilotNormalizedSignedLogVolume <= -weakThetaHullMagnitude,

proves it equivalent to the magnitude inequality T <= Q, and records the exact
numeric failure condition Q < T.  The inequality itself is not asserted.

No fake inequality, sign identification, carrier equivalence, sorry, axiom,
True, or PUnit is used. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.WeakSignedComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.WeakThetaHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.WeakDirectComparisonProofActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Raw Theta-hull magnitude candidate T = -weakThetaHullLogVolume.
This is the paper T when the actual weak Haar log-volume is the signed
quantity -T (i.e. nonpositive). -/
noncomputable def rawThetaHullMagnitude : Real :=
  -weakThetaHullLogVolume (I := I) C3

/-- Paper q-pilot magnitude Q = native global normalized q log magnitude. -/
noncomputable def nativeQPilotMagnitude : Real :=
  nativeGlobalQPilotNormalizedLogMagnitude T

theorem nativeQPilotMagnitude_eq :
    nativeQPilotMagnitude T = nativeGlobalQPilotNormalizedLogMagnitude T := rfl

/-- Correct signed comparison: weakThetaHullLogVolume (-T) is at least the
native signed q-pilot log-volume (-Q).  This is the direct paper direction
-T >= -Q, not a trivial comparison of a negative with a positive magnitude. -/
def WeakSignedComparison : Prop :=
  weakThetaHullLogVolume (I := I) C3 >=
    nativeGlobalQPilotNormalizedSignedLogVolume T

/-- The signed comparison is exactly the raw magnitude inequality T <= Q. -/
theorem weakSignedComparison_iff_raw :
    WeakSignedComparison (C3 := C3) T ↔
      rawThetaHullMagnitude (I := I) C3 <= nativeQPilotMagnitude T := by
  unfold WeakSignedComparison rawThetaHullMagnitude nativeQPilotMagnitude
    nativeGlobalQPilotNormalizedSignedLogVolume
  constructor <;> intro h <;> linarith

/-- Exact numeric failure condition: Q < T. -/
def WeakSignedComparisonObstacle : Prop :=
  nativeQPilotMagnitude T < rawThetaHullMagnitude (I := I) C3

/-- The signed comparison holds exactly when the numeric obstacle fails. -/
theorem weakSignedComparison_iff_not_obstacle :
    WeakSignedComparison (C3 := C3) T ↔
      ¬ WeakSignedComparisonObstacle (C3 := C3) T := by
  rw [weakSignedComparison_iff_raw]
  unfold WeakSignedComparisonObstacle
  constructor
  · intro h
    exact not_lt_of_ge h
  · intro h
    exact le_of_not_gt h

/-- The numeric obstacle refutes the signed comparison. -/
theorem not_weakSignedComparison_of_obstacle
    (h : WeakSignedComparisonObstacle (C3 := C3) T) :
    ¬ WeakSignedComparison (C3 := C3) T := by
  intro hc
  exact (weakSignedComparison_iff_not_obstacle (C3 := C3) T).mp hc h

/-- Exact sign condition needed to read weakThetaHullLogVolume as -T: the raw
Haar log-volume is nonpositive.  This is not proved for the unnormalized Haar
volume. -/
def WeakHullNonpositive : Prop :=
  weakThetaHullLogVolume (I := I) C3 <= 0

/-- Under the actual sign condition, the raw magnitude is the absolute value
of the weak Haar log-volume. -/
theorem rawThetaHullMagnitude_eq_abs_of_nonpositive
    (h : WeakHullNonpositive (C3 := C3)) :
    rawThetaHullMagnitude (C3 := C3) =
      |weakThetaHullLogVolume (I := I) C3| := by
  unfold rawThetaHullMagnitude
  rw [abs_of_nonpos h]
  ring

end LeanFormal.IUT.XiFPaper.WeakSignedComparisonActual

end
