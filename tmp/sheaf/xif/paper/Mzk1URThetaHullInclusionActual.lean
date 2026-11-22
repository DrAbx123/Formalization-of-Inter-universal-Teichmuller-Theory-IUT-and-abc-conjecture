/- R1.1 assembly: q-pilot sum equals -M_paper_v2 and -M <= ksThetaHullLogRoot_lam.

Full-fiber weights from david (DONE):
 * Mzk1ULOrdFiberTowerActual.MpaperB (l := l) T b  (= (1/(2l)) Qb per b),
 * Mzk1ULOrdFiberTowerActual.M_paper_v2_eq_sum_MpaperB : M_paper_v2 = Sum_b MpaperB_b.

Contents:
 * neg_Mpaper_v2_eq_sum_qPilotMass : with the per-b weight transfer
     MpaperB_b = - qPilotMass(cP_b)
   (the remaining per-b R0.1/R0.2 transfer, kept as an explicit hypothesis), the q-pilot sum is
   -M_paper_v2;
 * negM_le_thetaLam_of_perB : from the same identity and the per-b hull-log inequality
     qPilotMass(cP_b) <= thetaLamWeight_b * ksThetaHullLog_b
   conclude -M_paper_v2 <= ksThetaHullLogRoot_lam.
R0.2 SCALE: cPFullFiber_b = (1/[F:Q]) Sum_{P|b} f_P orderAtFPlace = ([Fmod_b:Q_p]/[Fmod:Q]) * cP_b
(the selected-lift qVFam c_P = v/e_abs enters only after this full-fiber weighting; no double /e).
The per-b inequality is exactly the geometric hull inclusion transported to log volumes
(candidate input: nu_ksThetaHull_le_nu_ceilRegion + urCeilRegion_logVolume + the procession source
map); it is kept explicit here, not faked.
-/
import tmp.sheaf.xif.paper.Mzk1ULOrdFiberTowerActual
import tmp.sheaf.xif.paper.Mzk1ULR1MpaperBWeightActual
import tmp.sheaf.xif.paper.Mzk1URRootNuOnePlaceActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaHullInclusionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1ULOrdFiberTowerActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootNuOnePlaceActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The q-pilot sum is -M_paper_v2 UNCONDITIONALLY, using david's per-b full-fiber weight
identity Mzk1ULR1MpaperBWeightActual.MpaperB_eq_neg_qPilotMass. -/
theorem neg_Mpaper_v2_eq_sum_qPilotMass :
    -LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (l := l) T =
      ∑ b : Bad (nativePlaceSelection T),
        qPilotMass (T := T) (b := b)
          (Mzk1ULR1MpaperBWeightActual.cPFullFiber (l := l) T b) := by
  rw [Mzk1ULOrdFiberTowerActual.M_paper_v2_eq_sum_MpaperB (l := l) T]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [Mzk1ULR1MpaperBWeightActual.MpaperB_eq_neg_qPilotMass (l := l) T b, neg_neg]

/-- -M_paper_v2 <= ksThetaHullLogRoot_lam from the per-b hull-log inequality. -/
theorem negM_le_thetaLam_of_perB (cP : Bad (nativePlaceSelection T) → ℝ)
    (hM : -LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (l := l) T =
      ∑ b : Bad (nativePlaceSelection T), qPilotMass (T := T) (b := b) (cP b))
    (hperB : ∀ b : Bad (nativePlaceSelection T),
      qPilotMass (T := T) (b := b) (cP b) ≤
        thetaLamWeight (l := l) T b * ksThetaHullLog (l := l) T b) :
    -LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (l := l) T ≤
      ksThetaHullLogRoot_lam (l := l) T := by
  rw [hM]
  unfold ksThetaHullLogRoot_lam
  exact Finset.sum_le_sum (fun b _ => hperB b)

#print axioms neg_Mpaper_v2_eq_sum_qPilotMass
#print axioms negM_le_thetaLam_of_perB


/-- R1 SINGLE OPEN (named, no proof): the per-b q-pilot log-mass is at most the weighted theta hull
log-volume.  Equivalently (route 3.2(5)): the per-b root lattice J_b is contained in the O-saturated
theta hull, and the normalized log-volume is monotone.  Recorded as the single R1 open statement. -/
def hperB_target : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    qPilotMass (T := T) (b := b) (Mzk1ULR1MpaperBWeightActual.cPFullFiber (l := l) T b) ≤
      thetaLamWeight (l := l) T b * ksThetaHullLog (l := l) T b

/-- -M_paper_v2 <= ksThetaHullLogRoot_lam from the per-b open hperB_target (assembly only). -/
theorem negM_le_thetaLam_of_hperB (h : hperB_target (l := l) T) :
    -LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (l := l) T ≤
      ksThetaHullLogRoot_lam (l := l) T :=
  negM_le_thetaLam_of_perB (l := l) T
    (Mzk1ULR1MpaperBWeightActual.cPFullFiber (l := l) T)
    (neg_Mpaper_v2_eq_sum_qPilotMass (l := l) T) h

#print axioms negM_le_thetaLam_of_hperB

end LeanFormal.IUT.XiFPaper.Mzk1URThetaHullInclusionActual
end