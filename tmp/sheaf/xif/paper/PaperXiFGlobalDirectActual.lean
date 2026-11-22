import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.PaperXiFSpec

/-!
# Paper xi-f target for the actual global q-pilot scalar

This file states the paper-level xi-f scalar directly in terms of the actual
native global q-pilot normalized log-volume, not via any identification with a
local C3 q parameter.

For

  M = nativeGlobalQPilotNormalizedLogMagnitude T,

we define the positive global q-pilot parameter q = exp(-M).  Its signed log is

  paperSignedLog q = -M,

because M >= 0.  Consequently paper xi-f is equivalent to the direct source
comparison

  nativeGlobalQPilotNormalizedSignedLogVolume T <= thetaHullLog.

No equality between a global q-pilot scalar and a local C3 q scalar is used or
required.  No inequality is asserted; the equivalence reduces the target to the
actual source comparison.  No sorry, axiom, True, or PUnit is used.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperXiFGlobalDirectActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual global q-pilot normalized log-magnitude is nonnegative. -/
theorem nativeGlobalQPilotNormalizedLogMagnitude_nonneg :
    0 <= nativeGlobalQPilotNormalizedLogMagnitude T := by
  unfold nativeGlobalQPilotNormalizedLogMagnitude
  apply Finset.sum_nonneg
  intro b _
  rw [nativeQPilotLocalNormalizedLogMagnitude_eq]
  exact mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg (localCompletionDegree T.arithmetic (nativeBadToKPlace T b))))
    (le_of_lt (baseQLogMagnitude_pos T b))

/-- The positive global q-pilot parameter defined directly from the actual
normalized log-magnitude. -/
noncomputable def globalPaperQParameter : Real :=
  Real.exp (-nativeGlobalQPilotNormalizedLogMagnitude T)

/-- The global q-pilot parameter is positive. -/
theorem globalPaperQParameter_pos : 0 < globalPaperQParameter T := by
  unfold globalPaperQParameter
  exact Real.exp_pos _

/-- Its log is the negative actual normalized magnitude. -/
theorem log_globalPaperQParameter_eq :
    Real.log (globalPaperQParameter T) =
      -nativeGlobalQPilotNormalizedLogMagnitude T := by
  unfold globalPaperQParameter
  rw [Real.log_exp]

/-- The signed paper log of the global q-pilot parameter is the actual signed
global q-pilot log-volume. -/
theorem paperSignedLog_globalPaperQParameter_eq :
    paperSignedLog (globalPaperQParameter T) =
      nativeGlobalQPilotNormalizedSignedLogVolume T := by
  unfold paperSignedLog nativeGlobalQPilotNormalizedSignedLogVolume
  rw [log_globalPaperQParameter_eq]
  rw [abs_neg, abs_of_nonneg (nativeGlobalQPilotNormalizedLogMagnitude_nonneg T)]

/-- Paper xi-f for the actual global q-pilot parameter is exactly the direct
source comparison, with no local/global q identification. -/
theorem paperXiF_global_iff (thetaHullLog : Real) :
    paperXiF (globalPaperQParameter T) thetaHullLog ↔
      nativeGlobalQPilotNormalizedSignedLogVolume T <= thetaHullLog := by
  unfold paperXiF paperHullRay
  rw [paperSignedLog_globalPaperQParameter_eq]
  rfl

/-- The paper xi-f statement for the global q-pilot parameter follows from the
direct source comparison. -/
theorem paperXiF_global_of_sourceComparison
    {thetaHullLog : Real}
    (h : nativeGlobalQPilotNormalizedSignedLogVolume T <= thetaHullLog) :
    paperXiF (globalPaperQParameter T) thetaHullLog :=
  (paperXiF_global_iff T thetaHullLog).mpr h

end LeanFormal.IUT.XiFPaper.PaperXiFGlobalDirectActual

end
