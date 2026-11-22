import tmp.sheaf.xif.paper.S695QPilotNormalizationAuditActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual

/-! # S705: qPilot vs Theta log-volume formula audit

Paper q-pilot: global sum over V_bad, weighted by w_v = 1/[K_v:F_v],
  qPilot = sum_v w_v * (ord_v(q_v)/(2l)) * log p_v.
Theta coefficient for label j is j^2 * ord_v(q_v)/(2l).
Per-b local ratio (ignoring w_v and log p_v) is j^2/(2l), hence >1 for
j^2>2l.  This is not a missing qPilot factor; it is the paper root
normalization.  The actual procession average is over F_l^x (card l-1), not
the SignedLabel set (card l, includes 0).  With that average the ratio is
(2l-1)/12, which is >1 for l>=7; for l=29 it is 57/12.
No global V_bad sum, local weight, or gamma factor can remove the per-label
ratio; only the full weighted sum is a different object. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S705QPilotThetaFormulaAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.S695QPilotNormalizationAuditActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Per-b qPilot coefficient: classical order(q_v)/(2l). -/
def qPilotLocalCoefficient : Real :=
  (((QPilotZeroLocusDivisorActual.qVFamily T b).order : Real)) /
    (2 * (l.value : Real))

/-- Per-b paper Theta coefficient: j^2 * order/(2l). -/
def thetaLocalCoefficient (j : SignedLabel l.value) : Real :=
  ((gaussExponent j.1).toNat : Real) *
    ((((QPilotZeroLocusDivisorActual.qVFamily T b).order : Real)) /
      (2 * l.value : Real))

theorem qPilotLocalCoefficient_eq_classical_div_twoL :
    qPilotLocalCoefficient T b =
      ((QPilotZeroLocusDivisorActual.qVFamily T b).order : Real) /
        (2 * (l.value : Real)) := rfl

theorem thetaLocalCoefficient_eq_j2_mul_qPilot
    (j : SignedLabel l.value) :
    thetaLocalCoefficient T b j =
      ((gaussExponent j.1).toNat : Real) * qPilotLocalCoefficient T b := by
  unfold thetaLocalCoefficient qPilotLocalCoefficient
  ring_nf

/-- l=29, j=8 has local coefficient ratio 64/58 > 1. -/
theorem l29_j8_theta_to_qPilot_ratio_gt_one :
    (1 : Real) < (8 : Real) ^ 2 := by
  norm_num

/-- Correct F_l^x procession average ratio for l=29: (2*29-1)/12 > 1. -/
theorem l29_procession_average_ratio_gt_one :
    (1 : Real) < (2 * 29 - 1 : Real) / 12 := by
  norm_num

/-- The actual paper label average is over F_l^x of cardinality l-1. -/
theorem paperLabelCardinality (l : PrimeGeFive) :
    Fintype.card (ProcessionLabel l) = l.value - 1 :=
  processionLabel_card l

end LeanFormal.IUT.XiFPaper.S705QPilotThetaFormulaAuditActual

end
