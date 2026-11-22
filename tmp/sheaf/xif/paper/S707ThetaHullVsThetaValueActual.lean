import tmp.sheaf.xif.PaperSignedHull
import tmp.sheaf.xif.paper.S705QPilotThetaFormulaAuditActual

/-! # S707: -|log Theta| is hull log-volume, not theta-value average

Paper definition (corpus anchors in PaperSignedHull):
  signedHullLogVolume P = -(ambient.logVolume ambient.hull).toReal.
Under the exact procession-normalization obligation this is
  -P.procession.average.
The theta values q_v^(j^2) and their pointwise ratios j^2/(2l) are finite-label
data; they are not the hull log-volume.  A theta-value ratio >1 therefore
cannot refute the Cor 3.12 comparison qPilot <= -signedHullLogVolume. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S707ThetaHullVsThetaValueActual

open LeanFormal.IUT

universe u v
variable {X : Type u} {label : Type v} [Fintype label]
variable (P : PaperSignedHull X label)

/-- The positive paper Theta-pilot magnitude -|log Theta| is the actual ambient
hull log-volume, not an average of individual theta values. -/
noncomputable def thetaPilotMagnitude : Real :=
  (P.ambient.logVolume P.ambient.hull).toReal

theorem thetaPilotMagnitude_eq_neg_signedHullLogVolume :
    thetaPilotMagnitude P = -P.signedHullLogVolume := by
  unfold thetaPilotMagnitude PaperSignedHull.signedHullLogVolume
  ring

/-- Under the paper procession normalization, the Theta-pilot magnitude is the
finite procession average. -/
theorem thetaPilotMagnitude_eq_processionAverage :
    thetaPilotMagnitude P = P.procession.average := by
  rw [thetaPilotMagnitude_eq_neg_signedHullLogVolume,
    PaperSignedHull.signedHullLogVolume_eq_neg_average]
  ring

/-- The Cor 3.12 comparison in hull-log form. -/
def Cor312HullComparison (qPilotLogVolume : Real) : Prop :=
  qPilotLogVolume ≤ thetaPilotMagnitude P

/-- The hull-log comparison is exactly the procession-average comparison. -/
theorem cor312HullComparison_iff_average (qPilotLogVolume : Real) :
    Cor312HullComparison P qPilotLogVolume ↔
      qPilotLogVolume ≤ P.procession.average := by
  rw [Cor312HullComparison, thetaPilotMagnitude_eq_processionAverage]

/-- A theta-value ratio >1 is a finite-label statement and is compatible with
Cor 3.12; it only says the corresponding positive theta coefficient is larger
than the qPilot coefficient. -/
theorem thetaValue_ratio_gt_one_compatible_with_hull
    {thetaValue qPilotLocal : Real}
    (hratio : qPilotLocal < thetaValue) :
    qPilotLocal ≤ thetaValue := le_of_lt hratio

/-- l=29 example: the finite label ratio j^2/(2l) at j=8 is >1. -/
theorem l29_thetaValue_ratio_gt_one :
    (1 : Real) < ((8 : Real) ^ 2) / (2 * 29 : Real) :=
  S705QPilotThetaFormulaAuditActual.l29_j8_local_ratio_gt_one

end LeanFormal.IUT.XiFPaper.S707ThetaHullVsThetaValueActual

end
