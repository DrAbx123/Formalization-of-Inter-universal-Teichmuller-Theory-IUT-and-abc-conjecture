/- G-C: GENERAL two-section map psi_general : Y_n ⟶ P¹ (route §4.1 L246-280).
   This file generalises Mzk1G1PsiFixedActual.psiFixed: instead of the fixed chart functions
   (psiChart0Coord, psiChartInfCoord) we accept arbitrary chart functions u0 (on chart 0) and
   u1 (on the infinity chart) together with the overlap compatibility. For the route's general
   Galois-stable finite T, u0 and u1 are the ratios s0/s1 produced from the divisor D_T by
   Riemann-Roch (donors found in-repo: AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor,
   AG_FLT_RiemannRochPromotionActual, AG12CechRiemannRochActual, AG06bRRInterfaceActual).
   Reuse: psiOpenCover / chartMorphism0 / chartMorphismInf / glueMorphisms pattern from
   Mzk1G1PsiFixedActual (this file only generalises the two chart functions). No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiFixedActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineCompatActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGlueCompatActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual

variable (n : Nat) (T : Finset ℚ)

/-- 一般 chart 函数：chart0 用 `u0`、chart∞ 用 `u1`（route §4.1 的 `s0/s1` 数据）。 -/
noncomputable def psiFunGeneral (u0 : R n) (u1 : Localization.Away (psiChartInfDenom n T)) :
    ∀ i : (psiOpenCover n T).I₀, (psiOpenCover n T).X i ⟶ projectiveLineGlued
  | ULift.up false => chartMorphism0 (R := R n) u0
  | ULift.up true => chartMorphismInf (R := Localization.Away (psiChartInfDenom n T)) u1

/-- overlap 兼容（route §4.1 的 `s0/s1` 一致性；由 RR 数据/函数域相等给出）。 -/
theorem glueMorphisms_compat_general (u0 : R n)
    (u1 : Localization.Away (psiChartInfDenom n T))
    (haffine : chart0ToOverlap n T ≫ chartMorphism0 (R := R n) u0 =
      chartInfPieceToOverlap n T ≫
        chartMorphismInf (R := Localization.Away (psiChartInfDenom n T)) u1) :
    ∀ x y : (psiOpenCover n T).I₀,
      pullback.fst ((psiOpenCover n T).f x) ((psiOpenCover n T).f y) ≫
          psiFunGeneral n T u0 u1 x =
        pullback.snd ((psiOpenCover n T).f x) ((psiOpenCover n T).f y) ≫
          psiFunGeneral n T u0 u1 y := by
  have hmixed : pullback.fst ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
      ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀)) ≫
        psiFunGeneral n T u0 u1 (ULift.up false) =
      pullback.snd ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
        ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀)) ≫
          psiFunGeneral n T u0 u1 (ULift.up true) := by
    have hw : wToPullback n T ≫
        (pullback.fst ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
            ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀)) ≫
              psiFunGeneral n T u0 u1 (ULift.up false))
      = wToPullback n T ≫
        (pullback.snd ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
            ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀)) ≫
              psiFunGeneral n T u0 u1 (ULift.up true)) := by
      rw [← Category.assoc, ← Category.assoc, wToPullback_fst, wToPullback_snd]
      exact haffine
    haveI : Epi (wToPullback n T) := inferInstance
    exact (cancel_epi (wToPullback n T)).mp hw
  intro x y
  obtain ⟨bx⟩ := x
  obtain ⟨by'⟩ := y
  cases bx <;> cases by'
  · dsimp only [psiFunGeneral]
    have hfs : pullback.fst ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
        ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀)) = pullback.snd _ _ := by
      rw [← cancel_mono ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))]
      rw [pullback.condition]
    rw [hfs]
  · dsimp only [psiFunGeneral]; exact hmixed
  · dsimp only [psiFunGeneral]
    haveI : Epi (pullbackSymmetry ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
        ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀))).hom := inferInstance
    rw [← cancel_epi (pullbackSymmetry ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
      ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀))).hom]
    rw [← Category.assoc, ← Category.assoc]
    rw [pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst]
    exact hmixed.symm
  · dsimp only [psiFunGeneral]
    have hfs : pullback.fst ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀))
        ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀)) = pullback.snd _ _ := by
      rw [← cancel_mono ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀))]
      rw [pullback.condition]
    rw [hfs]

/-- **route §4.1 的一般 ψ**：由 chart 函数 `u0`/`u1` 与 overlap 兼容粘出的 `Y_n ⟶ P¹`。 -/
noncomputable def psiGeneral (u0 : R n) (u1 : Localization.Away (psiChartInfDenom n T))
    (haffine : chart0ToOverlap n T ≫ chartMorphism0 (R := R n) u0 =
      chartInfPieceToOverlap n T ≫
        chartMorphismInf (R := Localization.Away (psiChartInfDenom n T)) u1) :
    fermatCurveScheme n ⟶ projectiveLineGlued :=
  (psiOpenCover n T).glueMorphisms (psiFunGeneral n T u0 u1)
    (glueMorphisms_compat_general n T u0 u1 haffine)

theorem psiGeneral_ι_false (u0 : R n) (u1 : Localization.Away (psiChartInfDenom n T))
    (haffine : chart0ToOverlap n T ≫ chartMorphism0 (R := R n) u0 =
      chartInfPieceToOverlap n T ≫
        chartMorphismInf (R := Localization.Away (psiChartInfDenom n T)) u1) :
    (psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀) ≫
        psiGeneral n T u0 u1 haffine = chartMorphism0 (R := R n) u0 :=
  Scheme.Cover.ι_glueMorphisms (𝒰 := psiOpenCover n T) (f := psiFunGeneral n T u0 u1)
    (hf := glueMorphisms_compat_general n T u0 u1 haffine) (ULift.up false : (psiOpenCover n T).I₀)

theorem psiGeneral_ι_true (u0 : R n) (u1 : Localization.Away (psiChartInfDenom n T))
    (haffine : chart0ToOverlap n T ≫ chartMorphism0 (R := R n) u0 =
      chartInfPieceToOverlap n T ≫
        chartMorphismInf (R := Localization.Away (psiChartInfDenom n T)) u1) :
    (psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀) ≫
        psiGeneral n T u0 u1 haffine =
      chartMorphismInf (R := Localization.Away (psiChartInfDenom n T)) u1 :=
  Scheme.Cover.ι_glueMorphisms (𝒰 := psiOpenCover n T) (f := psiFunGeneral n T u0 u1)
    (hf := glueMorphisms_compat_general n T u0 u1 haffine) (ULift.up true : (psiOpenCover n T).I₀)

#print axioms psiFunGeneral
#print axioms glueMorphisms_compat_general
#print axioms psiGeneral
#print axioms psiGeneral_ι_false
#print axioms psiGeneral_ι_true

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralActual
