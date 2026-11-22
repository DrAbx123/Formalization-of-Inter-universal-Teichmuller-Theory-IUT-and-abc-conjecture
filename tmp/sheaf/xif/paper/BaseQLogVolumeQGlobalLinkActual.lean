import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import tmp.sheaf.xif.paper.QPilotGlobalLogVolumeFromQActual

/-!
# Base q log-volume and qPilotQGlobalLogVolume: actual formulas/projections

Formulas for the actual native base q family:
* pointwise and total q-norm product;
* total signed log = negative total log magnitude;
* total log magnitude as the sum of the order times the log residue norm.

Connection to qside's qVFamily version:
* qPilotQGlobalLogVolume X is projected to the negative sum of the actual
  localLogMagnitude values of the qVFamily;
* the base q family's own norm-product formula is stated separately.

No cross-family equality is asserted (the base q family and qVFamily are
independent actual objects).  No inequality.  No Missing-only structure.  No
toy/True/PUnit/axiom/sorry.  WRITE-ONLY; no local compile; queued.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.BaseQLogVolumeQGlobalLinkActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual product of the base q norms over V_bad. -/
noncomputable def baseQNormProduct
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Real :=
  ∏ b : Bad (nativePlaceSelection T), ‖(baseQ T b).q‖

/-- Actual total q-norm formula: the product of the base q norms is the
exponential of the negative total log-magnitude. -/
theorem baseQNormProduct_eq_exp_neg_totalLogMagnitude
    [Fintype (Bad (nativePlaceSelection T))] :
    baseQNormProduct T = Real.exp (-baseQTotalLogMagnitude T) := by
  unfold baseQNormProduct baseQTotalLogMagnitude
  rw [Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro b _
  rw [baseQLogMagnitude, exp_neg_localLogMagnitude]

/-- Actual total signed-log formula: the total signed log is the sum of the
logs of the actual base q norms. -/
theorem baseQTotalSignedLog_eq_sum_log_norm
    [Fintype (Bad (nativePlaceSelection T))] :
    baseQTotalSignedLog T =
      ∑ b : Bad (nativePlaceSelection T), Real.log ‖(baseQ T b).q‖ := by
  unfold baseQTotalSignedLog baseQSignedLog localSignedLog
  rfl

/-- Actual total log-magnitude formula: sum over V_bad of order times the log
residue norm. -/
theorem baseQTotalLogMagnitude_eq_sum_order_mul_log
    [Fintype (Bad (nativePlaceSelection T))] :
    baseQTotalLogMagnitude T =
      ∑ b : Bad (nativePlaceSelection T),
        ((baseQ T b).order : Real) *
          Real.log (residueNormBase (nativeBaseSectionPlace T b)) := by
  unfold baseQTotalLogMagnitude
  apply Finset.sum_congr rfl
  intro b _
  exact baseQLogMagnitude_eq_order_mul_log T b

/-- Projection from the qside qVFamily log-volume object: it is the negative
sum of the actual qVFamily local log magnitudes. -/
theorem qPilotQGlobalLogVolume_qVFamily_projection
    (X : N8NativeInput l) [Fintype (Bad (nativePlaceSelection X.S))] :
    qPilotQGlobalLogVolume X =
      -∑ b : Bad (nativePlaceSelection X.S),
        localLogMagnitude (qVFamily X.S b) :=
  qPilotQGlobalLogVolume_eq_neg_sum_qVLogMagnitude X

end LeanFormal.IUT.XiFPaper.BaseQLogVolumeQGlobalLinkActual
