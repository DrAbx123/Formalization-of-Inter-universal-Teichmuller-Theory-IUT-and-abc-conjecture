/- B1④ (3)(4): intersection identity, pullback square, IsIso (wToPullback n T). -/
import tmp.sheaf.xif.paper.Mzk1G1PsiInterActual
import tmp.sheaf.xif.paper.Mzk1G1PsiRangeSupportActual
import tmp.sheaf.xif.paper.Mzk1G1PsiOverlapIsoActual
import Mathlib.Tactic
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiIsoActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineCompatActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiRangeSupportActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiInterActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiOverlapIsoActual
open scoped AlgebraicGeometry
variable (n : Nat) (T : Finset ℚ)
set_option maxHeartbeats 1600000 in
/-- (3) The intersection of the two chart pieces is the open range of the composite. -/
theorem inter_eq_composite_range :
    (fermatChart0ToCurve n).opensRange ⊓ (qPiece n T).opensRange =
      (chart0ToOverlap n T ≫ fermatChart0ToCurve n).opensRange := by
  haveI hc0 : IsOpenImmersion (fermatChart0ToCurve n) :=
    fermatChart0ToCurve_isOpenImmersion n
  haveI hci : IsOpenImmersion (fermatChartInfToCurve n) :=
    fermatChartInfToCurve_isOpenImmersion n
  haveI hq : IsOpenImmersion (qPiece n T) := qPiece_isOpenImmersion n T
  have hDq : (qPiece n T).opensRange ≤ (fermatChartInfToCurve n).opensRange := by
    rw [Mzk1G1PsiRangeSupportActual.qPiece_range n T]
    exact Scheme.Hom.image_le_opensRange (f := fermatChartInfToCurve n) _
  have h1 : (fermatChart0ToCurve n).opensRange ⊓ (qPiece n T).opensRange =
      ((fermatChart0ToCurve n).opensRange ⊓ (fermatChartInfToCurve n).opensRange) ⊓
        (qPiece n T).opensRange := by
    rw [inf_assoc, inf_eq_right.mpr hDq]
  have h2 : ((fermatChart0ToCurve n).opensRange ⊓
        (fermatChartInfToCurve n).opensRange) ⊓ (qPiece n T).opensRange =
      (fermatChartInfToCurve n ''ᵁ
        ((Spec (CommRingCat.of (ChartInfRing n))).basicOpen
          (Mzk1G1PsiRangeSupportActual.secOf (r1 n)))) ⊓
        (fermatChartInfToCurve n ''ᵁ
          ((Spec (CommRingCat.of (R2 n))).basicOpen
            (Mzk1G1PsiRangeSupportActual.secOf (psiChartInfDenom n T)))) := by
    rw [Mzk1G1PsiInterActual.inter_range n,
      Mzk1G1PsiRangeSupportActual.qPiece_range n T]
  have h3 : (fermatChartInfToCurve n ''ᵁ
        ((Spec (CommRingCat.of (ChartInfRing n))).basicOpen
          (Mzk1G1PsiRangeSupportActual.secOf (r1 n)))) ⊓
        (fermatChartInfToCurve n ''ᵁ
          ((Spec (CommRingCat.of (R2 n))).basicOpen
            (Mzk1G1PsiRangeSupportActual.secOf (psiChartInfDenom n T)))) =
      fermatChartInfToCurve n ''ᵁ
        (((Spec (CommRingCat.of (ChartInfRing n))).basicOpen
            (Mzk1G1PsiRangeSupportActual.secOf (r1 n))) ⊓
          ((Spec (CommRingCat.of (R2 n))).basicOpen
            (Mzk1G1PsiRangeSupportActual.secOf (psiChartInfDenom n T)))) := by
    rw [← Mzk1G1PsiInterActual.image_inf (fermatChartInfToCurve n)]
  have h4 : fermatChartInfToCurve n ''ᵁ
        (((Spec (CommRingCat.of (ChartInfRing n))).basicOpen
            (Mzk1G1PsiRangeSupportActual.secOf (r1 n))) ⊓
          ((Spec (CommRingCat.of (R2 n))).basicOpen
            (Mzk1G1PsiRangeSupportActual.secOf (psiChartInfDenom n T)))) =
      fermatChartInfToCurve n ''ᵁ
        ((Spec (CommRingCat.of (R2 n))).basicOpen
          (Mzk1G1PsiRangeSupportActual.secOf
            (psiChartInfDenom n T * chartR n))) := by
    congr 1
    rw [show r1 n = chartR n from rfl, inf_comm]
    exact (Mzk1G1PsiInterActual.basicOpen_mul n T).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans
    (Mzk1G1PsiRangeSupportActual.cY_range n T).symm)))
set_option maxHeartbeats 1600000 in
/-- H': the preimage of the D(q) piece under the first chart inclusion is the overlap. -/
theorem preimage_qPiece_range :
    (fermatChart0ToCurve n) ⁻¹ᵁ (qPiece n T).opensRange =
      (chart0ToOverlap n T).opensRange := by
  haveI hc0 : IsOpenImmersion (fermatChart0ToCurve n) :=
    fermatChart0ToCurve_isOpenImmersion n
  haveI hci : IsOpenImmersion (fermatChartInfToCurve n) :=
    fermatChartInfToCurve_isOpenImmersion n
  have hc : (fermatChart0ToCurve n) ''ᵁ (chart0ToOverlap n T).opensRange =
      (fermatChart0ToCurve n).opensRange ⊓ (qPiece n T).opensRange := by
    rw [← Scheme.Hom.opensRange_comp]
    exact (inter_eq_composite_range n T).symm
  have h := congrArg (fun U => (fermatChart0ToCurve n) ⁻¹ᵁ U) hc
  rw [Scheme.Hom.preimage_image_eq, Scheme.Hom.preimage_inf] at h
  have hU : (fermatChart0ToCurve n) ⁻¹ᵁ (fermatChart0ToCurve n).opensRange = ⊤ := by
    rw [← Scheme.Hom.image_top_eq_opensRange]
    exact Scheme.Hom.preimage_image_eq (fermatChart0ToCurve n) ⊤
  rw [hU, top_inf_eq] at h
  exact h.symm
set_option maxHeartbeats 1600000 in
/-- The square `chartInfPieceToOverlap/chart0ToOverlap/qPiece/fermatChart0ToCurve` is a pullback. -/
theorem isPullback_square :
    IsPullback (chartInfPieceToOverlap n T) (chart0ToOverlap n T)
      (qPiece n T) (fermatChart0ToCurve n) :=
  IsOpenImmersion.isPullback (chartInfPieceToOverlap n T) (chart0ToOverlap n T)
    (qPiece n T) (fermatChart0ToCurve n) (hcomp n T) (preimage_qPiece_range n T)
set_option maxHeartbeats 1600000 in
/-- The comparison map is the inverse of the pullback isomorphism: IsIso. -/
noncomputable instance isIso_wToPullback : IsIso (wToPullback n T) := by
  let h := isPullback_square n T
  let e : Spec (CommRingCat.of (overlapRing n T)) ≅
      pullback (fermatChart0ToCurve n) (qPiece n T) :=
    h.isoPullback ≪≫ pullbackSymmetry (qPiece n T) (fermatChart0ToCurve n)
  have hw : wToPullback n T = e.hom := by
    apply pullback.hom_ext
    · rw [wToPullback_fst]
      show chart0ToOverlap n T = e.hom ≫ pullback.fst _ _
      have h1 : e.hom ≫ pullback.fst (fermatChart0ToCurve n) (qPiece n T) =
          h.isoPullback.hom ≫ pullback.snd (qPiece n T) (fermatChart0ToCurve n) := by
        show (h.isoPullback ≪≫ pullbackSymmetry (qPiece n T) (fermatChart0ToCurve n)).hom ≫
            pullback.fst _ _ = _
        rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst]
      rw [h1, h.isoPullback_hom_snd]
    · rw [wToPullback_snd]
      show chartInfPieceToOverlap n T = e.hom ≫ pullback.snd _ _
      have h2 : e.hom ≫ pullback.snd (fermatChart0ToCurve n) (qPiece n T) =
          h.isoPullback.hom ≫ pullback.fst (qPiece n T) (fermatChart0ToCurve n) := by
        show (h.isoPullback ≪≫ pullbackSymmetry (qPiece n T) (fermatChart0ToCurve n)).hom ≫
            pullback.snd _ _ = _
        rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd]
      rw [h2, h.isoPullback_hom_fst]
  rw [hw]
  infer_instance
#print axioms isIso_wToPullback
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiIsoActual
