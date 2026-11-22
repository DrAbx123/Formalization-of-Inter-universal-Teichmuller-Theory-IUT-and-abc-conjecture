import tmp.sheaf.xif.paper.WeakKummerThetaValueActionActual
import tmp.sheaf.xif.paper.GlobalThetaPilotLogVolumeActual
import tmp.sheaf.xif.paper.GlobalQPilotProcessionLogVolumeActual

-- Weak Theta-hull magnitude vs q-pilot magnitude: corrected orientation
--
-- The paper direction is signed -|log Theta| >= -|log q|, equivalently
-- thetaHullMagnitude <= qPilotMagnitude (T <= Q). The previous
-- negative <= positive comparison was trivial and is removed. Here T is the
-- actual globalThetaPilotLogVolume and Q the actual globalQPilotLogMagnitude;
-- T = coefficient * Q. The inequality T <= Q is exactly coefficient <= 1;
-- if 1 < coefficient it is false. The coefficient bound is recorded as the
-- exact obstruction, not assumed. WRITE-ONLY: no local lake/lean.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.WeakThetaHullFromKummerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalQPilotProcessionLogVolumeActual
open LeanFormal.IUT.XiFPaper.WeakKummerThetaValueActionActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

-- The actual Theta-hull log-magnitude: the global Theta-pilot log-volume.
noncomputable def weakThetaHullLogMagnitude : Real :=
  globalThetaPilotLogVolume T

-- The corresponding signed Theta-hull log-volume: -|log Theta|.
noncomputable def weakThetaHullSignedLogVolume : Real :=
  -weakThetaHullLogMagnitude T

-- The actual q-pilot log-magnitude Q.
noncomputable def qPilotMagnitude : Real :=
  globalQPilotLogMagnitude T

-- The corresponding native signed q-pilot log-volume: -|log q|.
noncomputable def nativeGlobalQPilotNormalizedSignedLogVolume : Real :=
  -qPilotMagnitude T

-- The actual procession coefficient.
noncomputable def weakThetaHullCoefficient : Real :=
  (gaussExponentSum (l := l) : Real) /
    (Fintype.card (SignedLabel l.value) : Real)

-- Exact formula T = coefficient * Q.
theorem weakThetaHullLogMagnitude_eq :
    weakThetaHullLogMagnitude T =
      weakThetaHullCoefficient (l := l) * qPilotMagnitude T := by
  unfold weakThetaHullLogMagnitude qPilotMagnitude weakThetaHullCoefficient
  rw [globalThetaPilotLogVolume_eq]

-- The actual coefficient is nonnegative.
theorem weakThetaHullCoefficient_nonneg :
    0 ≤ weakThetaHullCoefficient (l := l) := by
  unfold weakThetaHullCoefficient
  apply div_nonneg <;> exact Nat.cast_nonneg _

section Nonempty

variable [Nonempty (Bad (nativePlaceSelection T))]

-- Exact equivalence: T <= Q iff the actual coefficient is at most one.
theorem weakThetaHullLogMagnitude_le_qPilot_iff :
    weakThetaHullLogMagnitude T ≤ qPilotMagnitude T ↔
      weakThetaHullCoefficient (l := l) ≤ 1 := by
  rw [weakThetaHullLogMagnitude_eq]
  have hQ : 0 < qPilotMagnitude T := by
    unfold qPilotMagnitude
    exact globalQPilotLogMagnitude_pos (T := T)
  constructor
  · intro h
    nlinarith [h, hQ]
  · intro h
    nlinarith [h, hQ]

-- Exact signed equivalence: -T >= -Q iff T <= Q.
theorem weakThetaHullSigned_ge_qPilotSigned_iff :
    weakThetaHullSignedLogVolume T ≥ nativeGlobalQPilotNormalizedSignedLogVolume T ↔
      weakThetaHullLogMagnitude T ≤ qPilotMagnitude T := by
  unfold weakThetaHullSignedLogVolume nativeGlobalQPilotNormalizedSignedLogVolume
  constructor <;> intro h <;> linarith

-- The coefficient bound is the exact missing estimate for the paper direction.
def WeakThetaHullCoefficientBound : Prop :=
  weakThetaHullCoefficient (l := l) ≤ 1

def WeakThetaHullMagnitudeInequalityRequired : Prop :=
  weakThetaHullLogMagnitude T ≤ qPilotMagnitude T

theorem magnitude_inequality_iff_coefficientBound :
    WeakThetaHullMagnitudeInequalityRequired (T := T) ↔
      WeakThetaHullCoefficientBound (l := l) :=
  weakThetaHullLogMagnitude_le_qPilot_iff (T := T)

-- If the coefficient is > 1, the target T <= Q is false.
theorem not_weakThetaHullLogMagnitude_le_qPilot_of_coeff_gt_one
    (hcoeff : 1 < weakThetaHullCoefficient (l := l)) :
    ¬ weakThetaHullLogMagnitude T ≤ qPilotMagnitude T := by
  intro h
  exact (not_le_of_gt hcoeff)
    ((weakThetaHullLogMagnitude_le_qPilot_iff (T := T)).mp h)

end Nonempty

#check weakThetaHullLogMagnitude
#check weakThetaHullSignedLogVolume
#check qPilotMagnitude
#check nativeGlobalQPilotNormalizedSignedLogVolume
#check weakThetaHullLogMagnitude_eq
#check weakThetaHullLogMagnitude_le_qPilot_iff
#check weakThetaHullSigned_ge_qPilotSigned_iff
#check WeakThetaHullCoefficientBound
#check WeakThetaHullMagnitudeInequalityRequired
#check not_weakThetaHullLogMagnitude_le_qPilot_of_coeff_gt_one

end LeanFormal.IUT.XiFPaper.WeakThetaHullFromKummerActual

end