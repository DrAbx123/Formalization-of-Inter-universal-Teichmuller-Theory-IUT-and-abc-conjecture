import tmp.sheaf.xif.paper.Mzk1G1PsiGlobalActual
import tmp.sheaf.xif.paper.Mzk1G1PsiOverlapIsoActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHcompRightActual
import tmp.sheaf.xif.paper.Mzk1SchemeOpensRangeInterfaceActual
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Tactic

/-! Support file for B1 step (3): range equalities of the two chart pieces. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiRangeSupportActual
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
open LeanFormal.IUT.XiFPaper.Mzk1SchemeOpensRangeInterfaceActual
open scoped AlgebraicGeometry

variable (n : Nat) (T : Finset ℚ)

/-- The section of the structure sheaf of Spec R corresponding to r : R. -/
def secOf {R : CommRingCat} (r : R) : Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv r

/-- The D(q) piece of the second chart: its open range. -/
theorem qPiece_range :
    (qPiece n T).opensRange =
      fermatChartInfToCurve n ''ᵁ
        (Spec (CommRingCat.of (R2 n))).basicOpen (secOf (psiChartInfDenom n T)) := by
  show (Spec.map (CommRingCat.ofHom
      (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)))) ≫
    fermatChartInfToCurve n).opensRange = _
  rw [Scheme.Hom.opensRange_comp]
  congr 1
  exact opensRange_localizationAway' (R := CommRingCat.of (R2 n))
    (g := psiChartInfDenom n T)

/-- The corresponding open range of the first chart leg (the intersection). -/
theorem cY_range :
    (chart0ToOverlap n T ≫ fermatChart0ToCurve n).opensRange =
      fermatChartInfToCurve n ''ᵁ
        (Spec (CommRingCat.of (R2 n))).basicOpen
          (secOf (psiChartInfDenom n T * chartR n)) := by
  have hmerge : Mzk1G1PsiAffineOverlapActual.chartInfPieceToOverlap n T ≫ qPiece n T =
      Spec.map (CommRingCat.ofHom
        (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T * chartR n)))) ≫
        fermatChartInfToCurve n := by
    show (Spec.map (CommRingCat.ofHom (qToOverlap n T)) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T))))) ≫
        fermatChartInfToCurve n = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Mzk1G1PsiHcompRightActual.qToOverlap_lift n T]
    rfl
  have hbasic :
      (Spec.map (CommRingCat.ofHom
        (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T * chartR n)))) ≫
        fermatChartInfToCurve n).opensRange =
      fermatChartInfToCurve n ''ᵁ
        (Spec (CommRingCat.of (R2 n))).basicOpen
          (secOf (psiChartInfDenom n T * chartR n)) := by
    rw [Scheme.Hom.opensRange_comp]
    congr 1
    exact opensRange_localizationAway' (R := CommRingCat.of (R2 n))
      (g := psiChartInfDenom n T * chartR n)
  rw [← hbasic]
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange]
  rw [show (chart0ToOverlap n T ≫ fermatChart0ToCurve n) =
    (Mzk1G1PsiAffineOverlapActual.chartInfPieceToOverlap n T ≫ qPiece n T)
    from hcomp n T]
  rw [hmerge]

#print axioms qPiece_range
#print axioms cY_range
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiRangeSupportActual
