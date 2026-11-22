/-
B1④ hcomp right leg (emmy's spec).  henry's ADAPTER file. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiAffineOverlapActual
import tmp.sheaf.xif.paper.Mzk1G1PsiCoverActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineGluedActual
import tmp.sheaf.xif.paper.Mzk1G1FermatOverlapActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveActual
import Mathlib.AlgebraicGeometry.Restrict
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiHcompRightActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open scoped AlgebraicGeometry
set_option maxHeartbeats 4000000 in
/-- qToOverlap is the lift of r2ToOverlap along the localization at q. -/
theorem qToOverlap_lift (n : Nat) (T : Finset ℚ) :
    (qToOverlap n T).comp
        (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T))) =
      r2ToOverlap n T :=
  IsLocalization.Away.lift_comp (S := Localization.Away (psiChartInfDenom n T))
    (x := psiChartInfDenom n T) (g := r2ToOverlap n T) (isUnit_q n T)
set_option maxHeartbeats 4000000 in
/-- infToOverlap is the lift of r2ToOverlap along the localization at r1. -/
theorem infToOverlap_lift (n : Nat) (T : Finset ℚ) :
    (infToOverlap n T).comp (algebraMap (ChartInfRing n) (OverlapInf n)) =
      r2ToOverlap n T :=
  IsLocalization.Away.lift_comp (S := OverlapInf n) (x := r1 n)
    (g := r2ToOverlap n T) (by
      have h : Mzk1G1PsiAffineOverlapActual.r2ToOverlap n T (Mzk1G1FermatOverlapActual.r1 n)
          = Mzk1G1PsiAffineOverlapActual.r2ToOverlap n T (Mzk1G1PsiChartMapsActual.chartR (n := n)) := rfl
      rw [h]; exact Mzk1G1PsiAffineOverlapActual.isUnit_r n T)
/-- The chart-infinity overlap inclusion is alpha followed by overlapToChartInf. -/
theorem overlapSpecMap10_comp_overlapToChartInf (n : Nat) :
    Spec.map (CommRingCat.ofHom (Mzk1G1FermatOverlapActual.alpha n)) ≫
        Mzk1G1FermatOverlapActual.overlapToChartInf n =
      Spec.map (CommRingCat.ofHom
        (algebraMap (ChartInfRing n) (OverlapInf n))) := by
  unfold Mzk1G1FermatOverlapActual.overlapToChartInf
  rw [show (Mzk1G1FermatOverlapActual.overlapSchemeIso n).hom =
      Mzk1G1FermatOverlapActual.overlapSpecMap01 n from rfl]
  rw [Mzk1G1FermatOverlapActual.overlapSpecMap01]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show (Mzk1G1FermatOverlapActual.alpha n).comp (Mzk1G1FermatOverlapActual.beta n)
      = RingHom.id (OverlapInf n) from Mzk1G1FermatOverlapActual.alpha_beta n]
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
/-- **B1④ hcomp, right leg.** -/
theorem hcomp_right_eq (n : Nat) (T : Finset ℚ) :
    chartInfPieceToOverlap n T ≫ qPiece n T =
      Spec.map (CommRingCat.ofHom (infToOverlap n T)) ≫
        Spec.map (CommRingCat.ofHom (Mzk1G1FermatOverlapActual.alpha n)) ≫
          Mzk1G1FermatOverlapActual.overlapToChartInf n ≫ fermatChartInfToCurve n := by
  rw [chartInfPieceToOverlap, qPiece]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [qToOverlap_lift n T]
  rw [← infToOverlap_lift n T]
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  rw [← overlapSpecMap10_comp_overlapToChartInf n]
  simp only [Category.assoc]
#print axioms qToOverlap_lift
#print axioms infToOverlap_lift
#print axioms overlapSpecMap10_comp_overlapToChartInf
#print axioms hcomp_right_eq
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiHcompRightActual