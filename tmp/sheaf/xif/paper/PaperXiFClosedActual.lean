import tmp.sheaf.xif.paper.GlobalQVFamThetaHullSumActual
import tmp.sheaf.xif.paper.NativeQVPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.PaperXiFSpec

/-!
# Paper xi-f from the actual qVFamily/global Theta-hull scalar

The global weighted q-pilot signed log and Theta-hull signed log have been
proved equal to the actual native qVFamily normalized signed scalar:

  globalQPilotLog = globalThetaHullLog
  = nativeQVPilotNormalizedSignedLogVolume.

Define q = exp(globalQPilotLog).  Since the signed scalar is nonpositive,
log q is that signed scalar and paperSignedLog q = log q.  Hence paper xi-f
  -|log q| <= -|log Theta|
holds with equality at the actual qVFamily scalar.

This is a scalar statement built from actual per-b fractional tensor data;
no LGP/Kummer/Ind compatibility and no carrier equivalence is used.  No
sorry, axiom, True, or PUnit is used.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperXiFClosedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullSumActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual global q parameter defined from the actual q-pilot signed log. -/
noncomputable def actualPaperQParameter : Real :=
  Real.exp (globalQPilotLog T)

/-- The q parameter is positive. -/
theorem actualPaperQParameter_pos : 0 < actualPaperQParameter T :=
  Real.exp_pos _

/-- Its log is the actual global q-pilot signed log. -/
theorem log_actualPaperQParameter :
    Real.log (actualPaperQParameter T) = globalQPilotLog T := by
  unfold actualPaperQParameter
  rw [Real.log_exp]

/-- The actual global q-pilot signed log is nonpositive. -/
theorem globalQPilotLog_nonpos : globalQPilotLog T <= 0 := by
  rw [globalQPilotLog_eq_nativeSigned]
  unfold nativeQVPilotNormalizedSignedLogVolume
  exact neg_nonpos.mpr (nativeQVPilotNormalizedLogMagnitude_nonneg T)

/-- The paper signed log of the actual q parameter is the global q-pilot log. -/
theorem paperSignedLog_actualPaperQParameter :
    paperSignedLog (actualPaperQParameter T) = globalQPilotLog T := by
  unfold paperSignedLog
  rw [log_actualPaperQParameter]
  rw [abs_of_nonpos (globalQPilotLog_nonpos T)]
  ring

/-- Paper xi-f holds at the actual qVFamily global q parameter with the actual
global Theta-hull signed log. -/
theorem paperXiF_actual :
    paperXiF (actualPaperQParameter T) (globalThetaHullLog T) := by
  rw [paperXiF_iff]
  rw [paperSignedLog_actualPaperQParameter]
  rw [globalQPilotLog_eq_nativeSigned, globalThetaHullLog_eq_nativeSigned]

/-- The paper-level scalar value of the actual q-pilot is the global signed log. -/
theorem paperSignedLog_actual_eq_global :
    paperSignedLog (actualPaperQParameter T) =
      nativeQVPilotNormalizedSignedLogVolume T := by
  rw [paperSignedLog_actualPaperQParameter, globalQPilotLog_eq_nativeSigned]

end LeanFormal.IUT.XiFPaper.PaperXiFClosedActual

end
