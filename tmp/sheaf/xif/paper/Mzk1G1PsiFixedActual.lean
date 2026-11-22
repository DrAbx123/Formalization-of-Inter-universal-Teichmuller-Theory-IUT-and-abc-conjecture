import tmp.sheaf.xif.paper.Mzk1G1PsiGlueCompatActual
import tmp.sheaf.xif.paper.Mzk1G1PsiAffineCompatActual
import tmp.sheaf.xif.paper.Mzk1G1PsiProductIdentityActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineBoundaryActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineTransitionActual
import Mathlib.Tactic
/-!
# B2 scheme version: the corrected two-section map `psiFixed` (route L273-278)

Henny's unconditional `psi` sends the protected chart coordinate `u = prod (x - t)`
into the *t-chart* of P^1 (`chartMorphismInf`), so `D_T` (where u = 0) maps to
`lambda = infinity`, not to 0.  Route §4.1 L273-278 (B2) requires `psi^{-1}(0) = D_T`.

This file swaps the two chart assignments on the same open cover:
`psiFixed` restricted to the first piece is `chartMorphism0 u` (lambda = u) and to the
second piece is `chartMorphismInf v` (t = v).  Compatibility follows from the existing
`affine_compat` plus `chartMorphism_transition` applied to the unit `psiUnit`.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
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
variable (n : Nat) (T : Finset ℚ)

/-- Swapped chart functions: first piece into the lambda-chart, second into the t-chart. -/
noncomputable def psiFunFixed :
    ∀ i : (psiOpenCover n T).I₀, (psiOpenCover n T).X i ⟶ projectiveLineGlued
  | ULift.up false => chartMorphism0 (R := R n) (psiChart0Coord n T)
  | ULift.up true =>
      chartMorphismInf (R := Localization.Away (psiChartInfDenom n T)) (psiChartInfCoord n T)

/-- Swapped affine compatibility on the overlap: lambda = u and t = v = u^{-1}. -/
theorem affine_compat_swapped :
    chart0ToOverlap n T ≫ chartMorphism0 (R := R n) (psiChart0Coord n T) =
      chartInfPieceToOverlap n T ≫
        chartMorphismInf (R := Localization.Away (psiChartInfDenom n T)) (psiChartInfCoord n T) := by
  rw [chart0ToOverlap, chartInfPieceToOverlap]
  rw [chartMorphism0_comp (f := rToOverlap n T) (hf := rToOverlap_rat n T)
    (a := psiChart0Coord n T)]
  rw [chartMorphismInf_comp (f := qToOverlap n T) (hf := qToOverlap_rat n T)
    (a := psiChartInfCoord n T)]
  rw [rToOverlap_coord n T, qToOverlap_coord n T]
  exact chartMorphism_transition (R := overlapRing n T) ((psiUnit n T)⁻¹)

/-- Compatibility of the swapped chart functions on the pullback. -/
theorem glueMorphisms_compat_fixed :
    ∀ x y : (psiOpenCover n T).I₀,
      pullback.fst ((psiOpenCover n T).f x) ((psiOpenCover n T).f y) ≫ psiFunFixed n T x =
        pullback.snd ((psiOpenCover n T).f x) ((psiOpenCover n T).f y) ≫ psiFunFixed n T y := by
  have hmixed : pullback.fst ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
      ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀)) ≫ psiFunFixed n T (ULift.up false) =
      pullback.snd ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
        ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀)) ≫ psiFunFixed n T (ULift.up true) := by
    have hw : wToPullback n T ≫
        (pullback.fst ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
            ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀)) ≫ psiFunFixed n T (ULift.up false))
      = wToPullback n T ≫
        (pullback.snd ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
            ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀)) ≫ psiFunFixed n T (ULift.up true)) := by
      rw [← Category.assoc, ← Category.assoc, wToPullback_fst, wToPullback_snd]
      exact affine_compat_swapped n T
    haveI : Epi (wToPullback n T) := inferInstance
    exact (cancel_epi (wToPullback n T)).mp hw
  intro x y
  obtain ⟨bx⟩ := x
  obtain ⟨by'⟩ := y
  cases bx <;> cases by'
  · dsimp only [psiFunFixed]
    have hfs : pullback.fst ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
        ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀)) = pullback.snd _ _ := by
      rw [← cancel_mono ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))]
      rw [pullback.condition]
    rw [hfs]
  · dsimp only [psiFunFixed]; exact hmixed
  · dsimp only [psiFunFixed]
    haveI : Epi (pullbackSymmetry ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
        ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀))).hom := inferInstance
    rw [← cancel_epi (pullbackSymmetry ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
      ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀))).hom]
    rw [← Category.assoc, ← Category.assoc]
    rw [pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst]
    exact hmixed.symm
  · dsimp only [psiFunFixed]
    have hfs : pullback.fst ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀))
        ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀)) = pullback.snd _ _ := by
      rw [← cancel_mono ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀))]
      rw [pullback.condition]
    rw [hfs]

/-- The corrected glued morphism `psiFixed : Y_n -> P^1` (lambda = u on the first piece). -/
noncomputable def psiFixed : fermatCurveScheme n ⟶ projectiveLineGlued :=
  (psiOpenCover n T).glueMorphisms (psiFunFixed n T) (glueMorphisms_compat_fixed n T)

theorem psiFixed_ι_false :
    (psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀) ≫ psiFixed n T =
      chartMorphism0 (R := R n) (psiChart0Coord n T) :=
  Scheme.Cover.ι_glueMorphisms (𝒰 := psiOpenCover n T) (f := psiFunFixed n T)
    (hf := glueMorphisms_compat_fixed n T) (ULift.up false : (psiOpenCover n T).I₀)

theorem psiFixed_ι_true :
    (psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀) ≫ psiFixed n T =
      chartMorphismInf (R := Localization.Away (psiChartInfDenom n T)) (psiChartInfCoord n T) :=
  Scheme.Cover.ι_glueMorphisms (𝒰 := psiOpenCover n T) (f := psiFunFixed n T)
    (hf := glueMorphisms_compat_fixed n T) (ULift.up true : (psiOpenCover n T).I₀)

#print axioms affine_compat_swapped
#print axioms glueMorphisms_compat_fixed
#print axioms psiFixed
#print axioms psiFixed_ι_false
#print axioms psiFixed_ι_true
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
end