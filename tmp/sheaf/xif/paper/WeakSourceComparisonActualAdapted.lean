import tmp.sheaf.xif.paper.PaperXiFGlobalDirectActual
import tmp.sheaf.xif.paper.GlobalThetaPilotLogVolumeActual
import tmp.sheaf.xif.paper.GlobalQPilotProcessionLogVolumeActual

/-!
# Signed weak source comparison: corrected target and exact obstruction

The previous target

  paperSignedLog q <= thetaHullRawScalar

with thetaHullRawScalar a positive raw Theta magnitude was the trivial
negative <= positive comparison.  It is not the paper signed comparison.

The paper signed comparison is

  paperSignedLog q <= P.signedHullLogVolume,

where P.signedHullLogVolume = -|log Theta| is the negative signed hull volume.
For the raw Theta scalar thetaHullRawScalar = |log Theta| this is

  paperSignedLog q <= -thetaHullRawScalar T,

equivalently

  thetaHullRawScalar T <= nativeGlobalQPilotNormalizedLogMagnitude T.

This file states that corrected target, proves the exact equivalence, and gives
the exact obstruction/refutation condition for the current raw Theta scalar.  It
does not prove the inequality unconditionally and does not replace it by the
trivial negative <= positive estimate.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.WeakSourceComparisonActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalQPilotProcessionLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.PaperXiFGlobalDirectActual
open LeanFormal.IUT.XiFPaper.PaperXiFSpec
open LeanFormal.IUT.XiFPaper.SignedAverageBoundActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual signed global q-pilot scalar from the weighted bad-q sum. -/
noncomputable def weightedQMagnitudeSum : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * baseQLogMagnitude T b

/-- The actual signed q scalar. -/
noncomputable def weakQScalar : Real :=
  nativeGlobalQPilotNormalizedSignedLogVolume T

/-- The signed q scalar is the negative weighted q magnitude. -/
theorem weakQScalar_eq :
    weakQScalar T = -weightedQMagnitudeSum T := by
  unfold weakQScalar weightedQMagnitudeSum
  rw [nativeGlobalQPilotNormalizedSignedLogVolume,
    nativeGlobalQPilotNormalizedLogMagnitude_eq]

/-- The actual raw positive Theta-pilot magnitude. -/
noncomputable def thetaHullRawScalar : Real :=
  globalThetaPilotLogVolume T

/-- The actual signed Theta-pilot hull scalar -|log Theta|. -/
noncomputable def thetaHullSignedScalar : Real :=
  -thetaHullRawScalar T

/-- The corrected paper signed target. -/
def WeakSignedSourceComparison : Prop :=
  paperSignedLog (globalPaperQParameter T) <= thetaHullSignedScalar T

/-- Exact equivalence of the signed target with the raw magnitude comparison. -/
theorem weakSignedSourceComparison_iff_raw :
    WeakSignedSourceComparison T ↔
      thetaHullRawScalar T <= nativeGlobalQPilotNormalizedLogMagnitude T := by
  unfold WeakSignedSourceComparison thetaHullSignedScalar
  rw [paperSignedLog_globalPaperQParameter_eq]
  unfold nativeGlobalQPilotNormalizedSignedLogVolume
  constructor <;> intro h <;> linarith

/-- The raw Theta scalar is the Gauss coefficient times the unweighted global
q magnitude. -/
theorem thetaHullRawScalar_eq :
    thetaHullRawScalar T =
      ((gaussExponentSum (l := l) : Real) /
        (Fintype.card (SignedLabel l.value) : Real)) *
        globalQPilotLogMagnitude T := by
  unfold thetaHullRawScalar
  exact globalThetaPilotLogVolume_eq

/-- Exact obstruction: the signed paper target is exactly the raw comparison
above; this is the condition that remains to be proved. -/
def WeakSignedSourceComparisonObstruction : Prop :=
  thetaHullRawScalar T <= nativeGlobalQPilotNormalizedLogMagnitude T

/-- The target is exactly the obstruction. -/
theorem weakSignedSourceComparison_iff_obstruction :
    WeakSignedSourceComparison T ↔ WeakSignedSourceComparisonObstruction T :=
  weakSignedSourceComparison_iff_raw T

/-- Actual refutation condition: if the raw Gauss coefficient is strictly
greater than one and the weighted q magnitude is at most the unweighted q
magnitude, then the raw comparison (hence the signed paper target) fails. -/
theorem not_weakSignedSourceComparison_of_coeff_gt_one
    (hcoef : 1 <
      (gaussExponentSum (l := l) : Real) /
        (Fintype.card (SignedLabel l.value) : Real))
    (hM : nativeGlobalQPilotNormalizedLogMagnitude T <=
      globalQPilotLogMagnitude T)
    (hU : 0 < globalQPilotLogMagnitude T) :
    ¬ WeakSignedSourceComparison T := by
  intro h
  have hraw := (weakSignedSourceComparison_iff_raw T).mp h
  rw [thetaHullRawScalar_eq] at hraw
  have hlt : globalQPilotLogMagnitude T <
      ((gaussExponentSum (l := l) : Real) /
        (Fintype.card (SignedLabel l.value) : Real)) *
        globalQPilotLogMagnitude T := by
    nlinarith [hcoef, hU]
  linarith

/-- The current signed target is not the trivial negative <= positive
estimate: its right side is the negative thetaHullRawScalar. -/
theorem weakSignedSourceComparison_target_sign :
    WeakSignedSourceComparison T ↔
      paperSignedLog (globalPaperQParameter T) <= -thetaHullRawScalar T :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.WeakSourceComparisonActualAdapted

end
