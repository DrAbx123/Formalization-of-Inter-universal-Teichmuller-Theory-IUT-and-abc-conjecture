import tmp.sheaf.xif.paper.Mzk1G1PsiGlobalActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHcompRightActual
import tmp.sheaf.xif.paper.Mzk1G1PsiAffineCompatActual
import tmp.sheaf.xif.paper.Mzk1G1PsiCoverActual
import Mathlib.Tactic

/-! # M2 route to IsIso (wToPullback n T): open-immersion steps.

Step (a): the localization map R2 -> Away(q*r) is an open immersion (free).
Steps (b)(c): chartInfPieceToOverlap / chart0ToOverlap are open immersions, obtained
with MorphismProperty.of_postcomp from the fact that their composites with the chart
inclusions of Y_n are the same open immersion (hcomp + r2ToOverlap localization +
fermatChartInfToCurve).  Step (2): wToPullback is an open immersion, again by of_postcomp
(wToPullback ≫ pullback.fst = chart0ToOverlap, pullback.fst is a base change of the open
immersion qPiece). -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiOverlapIsoActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartInfCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineCompatActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHcompRightActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual

variable (n : Nat) (T : Finset ℚ)

/-- STEP (a): the localization map R2 -> Away(q*r) is an open immersion. -/
instance isOpenImmersion_r2ToOverlap_away :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T * chartR n))))) := by
  infer_instance

/-- The composite `chart0ToOverlap ≫ fermatChart0ToCurve` is the open immersion
`Spec(Away(q*r)) ⟶ Y_n`.  Via hcomp it equals the q-piece composite. -/
theorem isOpenImmersion_chart0ToCurve_composite :
    IsOpenImmersion (chart0ToOverlap n T ≫ fermatChart0ToCurve n) := by
  rw [hcomp n T]
  show IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (qToOverlap n T)) ≫
      (Spec.map (CommRingCat.ofHom
        (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)))) ≫
        fermatChartInfToCurve n))
  rw [← Category.assoc]
  have hstep : Spec.map (CommRingCat.ofHom (qToOverlap n T)) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T * chartR n)))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, qToOverlap_lift n T]
    rfl
  rw [hstep]
  exact IsOpenImmersion.comp _ _

/-- STEP (c): chart0ToOverlap is an open immersion. -/
instance isOpenImmersion_chart0ToOverlap :
    IsOpenImmersion (chart0ToOverlap n T) :=
  MorphismProperty.of_postcomp (W := @IsOpenImmersion) (W' := @IsOpenImmersion) (f := chart0ToOverlap n T)
    (g := fermatChart0ToCurve n) (inferInstance)
    (isOpenImmersion_chart0ToCurve_composite n T)

/-- The composite `chartInfPieceToOverlap ≫ qPiece` is an open immersion (same open). -/
theorem isOpenImmersion_chartInfPiece_composite :
    IsOpenImmersion (chartInfPieceToOverlap n T ≫ qPiece n T) := by
  rw [← hcomp n T]
  exact isOpenImmersion_chart0ToCurve_composite n T

/-- STEP (b): chartInfPieceToOverlap is an open immersion. -/
instance isOpenImmersion_chartInfPieceToOverlap :
    IsOpenImmersion (chartInfPieceToOverlap n T) :=
  MorphismProperty.of_postcomp (W := @IsOpenImmersion) (W' := @IsOpenImmersion) (f := chartInfPieceToOverlap n T)
    (g := qPiece n T) (inferInstance)
    (isOpenImmersion_chartInfPiece_composite n T)

/-- STEP (2): the comparison map to the pullback is an open immersion. -/
instance isOpenImmersion_wToPullback : IsOpenImmersion (wToPullback n T) := by
  refine MorphismProperty.of_postcomp (W := @IsOpenImmersion) (W' := @IsOpenImmersion) (f := wToPullback n T)
    (g := pullback.fst ((psiOpenCover n T).f (ULift.up false))
      ((psiOpenCover n T).f (ULift.up true))) (inferInstance) ?_
  rw [wToPullback_fst]
  exact isOpenImmersion_chart0ToOverlap n T

#print axioms isOpenImmersion_chart0ToCurve_composite
#print axioms isOpenImmersion_wToPullback
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiOverlapIsoActual