import tmp.sheaf.xif.PaperSignedHull
noncomputable section
set_option maxHeartbeats 1000000
namespace LeanFormal.IUT.XiFPaper.S2137PaperHullNormalizationActual
open LeanFormal.IUT
variable {X : Type} {label : Type} [Fintype label]
variable (P : PaperSignedHull X label)
/-- Exact scalar input for the paper hull normalization: the procession average
is the negative logarithm of the actual root-stack Theta scalar. -/
def s2137HullAverageNormalization (rootStackTheta : Real) : Prop :=
  P.procession.average = - Real.log rootStackTheta
/-- **Paper hull normalization from the average identification.**
If the procession average is `-log rootStackTheta`, then the signed hull
log-volume is `log rootStackTheta`. -/
theorem s2137_signedHull_eq_log_rootStackTheta_of_average
    {rootStackTheta : Real}
    (h : s2137HullAverageNormalization P rootStackTheta) :
    P.signedHullLogVolume = Real.log rootStackTheta := by
  unfold s2137HullAverageNormalization at h
  rw [PaperSignedHull.signedHullLogVolume_eq_neg_average P, h, neg_neg]
/-- Ambient `ENNReal` form of the same reduction: if the actual hull
log-volume has real value `-log rootStackTheta`, then the signed hull
log-volume is `log rootStackTheta`. -/
theorem s2137_signedHull_eq_log_rootStackTheta_of_ambient
    {rootStackTheta : Real}
    (h : (P.ambient.logVolume P.ambient.hull).toReal = - Real.log rootStackTheta) :
    P.signedHullLogVolume = Real.log rootStackTheta := by
  unfold PaperSignedHull.signedHullLogVolume
  rw [h, neg_neg]
/-- The exact missing scalar equality after the reduction: the procession
average must be `-log rootStackTheta`. -/
def s2137FirstMissing (rootStackTheta : Real) : Prop :=
  s2137HullAverageNormalization P rootStackTheta
#print axioms s2137_signedHull_eq_log_rootStackTheta_of_average
#print axioms s2137_signedHull_eq_log_rootStackTheta_of_ambient
end LeanFormal.IUT.XiFPaper.S2137PaperHullNormalizationActual
end
