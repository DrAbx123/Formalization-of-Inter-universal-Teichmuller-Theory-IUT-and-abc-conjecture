/- Support facts for the lambda-coordinate morphism `hPolyL`/`phiFixedL` (route B1). -/
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaFactsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual

/-- The first chart piece of `phiFixedL` is the chart map of `psiFixed` composed with `hPolyL`. -/
theorem phiFixedL_ι_false (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) :
    (psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀) ≫ phiFixedL n T h hh =
      chartMorphism0 (R := R n) (psiChart0Coord n T) ≫ hPolyL h hh := by
  rw [phiFixedL, ← Category.assoc, psiFixed_ι_false]
  rfl

/-- The second chart piece of `phiFixedL`. -/
theorem phiFixedL_ι_true (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) :
    (psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀) ≫ phiFixedL n T h hh =
      chartMorphismInf (R := Localization.Away (psiChartInfDenom n T)) (psiChartInfCoord n T) ≫
        hPolyL h hh := by
  rw [phiFixedL, ← Category.assoc, psiFixed_ι_true]
  rfl

/-- The lambda-chart formula of `phiFixedL` on the first chart piece:
`lambda' = h(u)` with `u = psiChart0Coord`. -/
theorem phiFixedL_chart0 (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) :
    (psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀) ≫ phiFixedL n T h hh =
      chartMorphism0 (R := R n) (Polynomial.aeval (psiChart0Coord n T) h) := by
  rw [phiFixedL_ι_false]
  show Spec.map (CommRingCat.ofHom (Mzk1G1ProjectiveLineTransitionActual.evalAt
      (R := R n) (psiChart0Coord n T))) ≫ localChart0 ≫ hPolyL h hh = _
  rw [hPolyL_lambda_chart h hh]
  rw [specMap_chartMorphism0 (R := Polynomial ℚ) (S := R n)
    (Mzk1G1ProjectiveLineTransitionActual.evalAt (R := R n) (psiChart0Coord n T))
    (by exact RingHom.ext_rat _ _) h]
  rfl

#print axioms phiFixedL_ι_false
#print axioms phiFixedL_ι_true
#print axioms phiFixedL_chart0
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaFactsActual
-- t