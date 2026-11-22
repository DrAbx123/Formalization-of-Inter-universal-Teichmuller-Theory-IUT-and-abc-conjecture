import tmp.sheaf.xif.paper.GlobalPositiveHullFromCorrectedActual
import tmp.sheaf.xif.paper.PaperXiFGlobalDirectActual
import tmp.sheaf.xif.paper.PaperXiFSpec

/-!
# Sign-correct paper xi-f target for the corrected positive Theta hull

This file uses the corrected positive Theta hull log-volume

  globalPositiveThetaHullLogVolume

from GlobalPositiveHullFromCorrectedActual (supremum of positive point
log-volumes), not the old zero-truncated sourceHullVolume.

Let

  Q = nativeQPilotComparisonMagnitude T  (> 0),
  T = globalPositiveThetaHullLogVolume I R n.

The paper q parameter is

  q = exp(-Q).

Then log q = -Q and paperSignedLog q = -Q.  The signed Theta hull volume is
-T.  Paper xi-f

  -|log q| <= -|log Theta|

is therefore exactly

  -Q <= -T, i.e. T <= Q.

No equality between global and local objects is used.  No inequality is
asserted; the equivalence reduces the paper statement to the actual scalar
comparison.  No sorry, axiom, True, PUnit, or toy object is used.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.GlobalPositiveHullPaperXiFActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.GlobalPositiveHullFromCorrectedActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.PaperXiFGlobalDirectActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : forall v : V, I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual global q parameter defined from the negative normalized
magnitude. -/
noncomputable def positiveGlobalPaperQParameter : Real :=
  Real.exp (-nativeQPilotComparisonMagnitude T)

/-- Its log is the negative actual normalized magnitude. -/
theorem log_positiveGlobalPaperQParameter :
    Real.log (positiveGlobalPaperQParameter T) =
      -nativeQPilotComparisonMagnitude T := by
  unfold positiveGlobalPaperQParameter
  rw [Real.log_exp]

/-- Its signed paper log is the negative actual normalized magnitude. -/
theorem paperSignedLog_positiveGlobalPaperQParameter :
    paperSignedLog (positiveGlobalPaperQParameter T) =
      -nativeQPilotComparisonMagnitude T := by
  unfold paperSignedLog
  rw [log_positiveGlobalPaperQParameter]
  rw [nativeQPilotComparisonMagnitude_eq T]
  rw [abs_neg, abs_of_nonneg (nativeGlobalQPilotNormalizedLogMagnitude_nonneg T)]

/-- The signed Theta hull scalar from the corrected positive hull. -/
noncomputable def positiveGlobalThetaHullSigned : Real :=
  -globalPositiveThetaHullLogVolume (I := I) R n

/-- Paper xi-f for the corrected positive hull is exactly the actual scalar
comparison T <= Q. -/
theorem paperXiF_globalPositiveHull_iff :
    paperXiF (positiveGlobalPaperQParameter T)
        (positiveGlobalThetaHullSigned (I := I) R n) ↔
      globalPositiveThetaHullLogVolume (I := I) R n <=
        nativeQPilotComparisonMagnitude T := by
  rw [paperXiF_iff]
  unfold positiveGlobalThetaHullSigned
  rw [paperSignedLog_positiveGlobalPaperQParameter]
  constructor <;> intro h <;> linarith

/-- Paper xi-f follows from the explicit actual comparison T <= Q. -/
theorem paperXiF_globalPositiveHull_of_comparison
    (h : globalPositiveThetaHullLogVolume (I := I) R n <=
      nativeQPilotComparisonMagnitude T) :
    paperXiF (positiveGlobalPaperQParameter T)
      (positiveGlobalThetaHullSigned (I := I) R n) :=
  (paperXiF_globalPositiveHull_iff (I := I) R n T).mpr h

end LeanFormal.IUT.XiFPaper.GlobalPositiveHullPaperXiFActual

end
