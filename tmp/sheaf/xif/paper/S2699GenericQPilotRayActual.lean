import tmp.sheaf.xif.PaperSignedHull
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2699GenericQPilotRayActual

open LeanFormal.IUT

/-- Generic q-pilot ray inclusion from a bad-q absolute-log lower bound.

`qPilotLogVolume = -badQAbsLog`; the signed hull volume is `-P.average`.
If the raw signed hull average is `2 log 5` and `2 log 5 ≤ badQAbsLog`, then
the q-pilot scalar lies in the Step (xi-f) ray.  This is place-count
agnostic: it applies to the upcoming three/four-place `V_bad` once the
`S2696BadQAbsLog` sum is identified with `badQAbsLog`. -/
theorem S2699_qPilot_mem_ray_of_badQAbsLog_ge
    {X : Type} {label : Type} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average = 2 * Real.log 5)
    (badQAbsLog : Real)
    (hbad : 2 * Real.log 5 ≤ badQAbsLog) :
    -badQAbsLog ∈ hullLogVolumeRay P.signedHullLogVolume := by
  rw [mem_hullLogVolumeRay_iff,
    PaperSignedHull.signedHullLogVolume_eq_neg_average P, hP]
  linarith

/-- The comparison form of the same criterion. -/
theorem S2699_qPilot_mem_ray_iff_comparison
    {X : Type} {label : Type} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average = 2 * Real.log 5)
    (badQAbsLog : Real) :
    -badQAbsLog ∈ hullLogVolumeRay P.signedHullLogVolume ↔
      2 * Real.log 5 ≤ badQAbsLog := by
  rw [mem_hullLogVolumeRay_iff,
    PaperSignedHull.signedHullLogVolume_eq_neg_average P, hP]
  constructor <;> intro h <;> linarith

/-- Four-place `V_bad` lower-bound form: if the four-term bad-q absolute log is
at least `2 log 5 + 2 log 2161`, then the q-pilot scalar lies in the
Step (xi-f) ray.  The old singleton/two-place bounds are not used. -/
theorem S2699_qPilot_mem_ray_of_fourPlace_lower
    {X : Type} {label : Type} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average = 2 * Real.log 5)
    (badQAbsLog : Real)
    (hbad : 2 * Real.log 5 + 2 * Real.log 2161 ≤ badQAbsLog) :
    -badQAbsLog ∈ hullLogVolumeRay P.signedHullLogVolume := by
  apply S2699_qPilot_mem_ray_of_badQAbsLog_ge P hP
  have hlog2161 : (0 : Real) ≤ Real.log 2161 :=
    Real.log_nonneg (by norm_num)
  linarith

#check S2699_qPilot_mem_ray_of_badQAbsLog_ge
#check S2699_qPilot_mem_ray_of_fourPlace_lower
#check S2699_qPilot_mem_ray_iff_comparison
#print axioms S2699_qPilot_mem_ray_of_badQAbsLog_ge

end LeanFormal.IUT.XiFPaper.S2699GenericQPilotRayActual
end
