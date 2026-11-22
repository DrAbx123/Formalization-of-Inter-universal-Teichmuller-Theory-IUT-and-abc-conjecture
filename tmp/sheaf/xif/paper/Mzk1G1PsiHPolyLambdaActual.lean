/- P^1 coordinate version `hPolyL` of `hPoly`, the composite `phiFixedL`, and the
chart formulas (route §4.4 / B1). `hPoly` acts in the t-coordinate (`t ↦ h(t)`);
the B1-compatible version acts in the lambda-coordinate:
  `hPolyL := p1Inv ≫ hPoly ≫ p1Inv`   (so that `lambda' = h(lambda)`).

Design: `Mzk1G1PsiHPolyLambdaSpec.md`. `p1Inv` is grace's `Mzk1G1PsiP1InvActual`.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiP1InvActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyFinalActual
import tmp.sheaf.xif.paper.Mzk1G1PsiFixedActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual



/-- The lambda-coordinate version of `hPoly`: `p1Inv ≫ hPoly ≫ p1Inv`. -/
noncomputable def hPolyL (h : Polynomial ℚ) (hh : h ≠ 0) : projectiveLineGlued ⟶ projectiveLineGlued :=
  p1Inv ≫ hPoly h hh ≫ p1Inv

theorem hPolyL_def (h : Polynomial ℚ) (hh : h ≠ 0) : hPolyL h hh = p1Inv ≫ hPoly h hh ≫ p1Inv := rfl

/-- Evaluation of a polynomial at the chart variable is the identity. -/
theorem evalAt_X_self (p : Polynomial ℚ) :
    Mzk1G1ProjectiveLineTransitionActual.evalAt (R := Polynomial ℚ) Polynomial.X p = p := by
  simp [Mzk1G1ProjectiveLineTransitionActual.evalAt]

/-- `chartMorphismInf X` composed with `hPoly` is `chartMorphismInf h` (t' = h(t)). -/
theorem chartMorphismInf_X_comp_hPoly (h : Polynomial ℚ) (hh : h ≠ 0) :
    chartMorphismInf (R := Polynomial ℚ) Polynomial.X ≫ hPoly h hh =
      chartMorphismInf (R := Polynomial ℚ) h := by
  show Spec.map (CommRingCat.ofHom (Mzk1G1ProjectiveLineTransitionActual.evalAt
      (R := Polynomial ℚ) Polynomial.X)) ≫ localChartInf ≫ hPoly h hh = _
  rw [show localChartInf ≫ hPoly h hh =
      chartMorphismInf (R := Polynomial ℚ) h from by
    rw [show localChartInf = (hPolyCover h hh).f HIdx.c0 from rfl]
    exact hPoly_ι_c0 h hh]
  rw [specMap_chartMorphismInf (R := Polynomial ℚ) (S := Polynomial ℚ)
    (Mzk1G1ProjectiveLineTransitionActual.evalAt (R := Polynomial ℚ) Polynomial.X)
    (by exact RingHom.ext_rat _ _) h, evalAt_X_self h]

/-- `chartMorphismInf h` composed with `p1Inv` is `chartMorphism0 h` (lambda' = h). -/
theorem chartMorphismInf_comp_p1Inv (h : Polynomial ℚ) :
    chartMorphismInf (R := Polynomial ℚ) h ≫ p1Inv =
      chartMorphism0 (R := Polynomial ℚ) h := by
  show Spec.map (CommRingCat.ofHom (Mzk1G1ProjectiveLineTransitionActual.evalAt
      (R := Polynomial ℚ) h)) ≫ localChartInf ≫ p1Inv = _
  rw [show localChartInf ≫ p1Inv =
      chartMorphism0 (R := Polynomial ℚ) Polynomial.X from p1Inv_ι_true]
  rw [specMap_chartMorphism0 (R := Polynomial ℚ) (S := Polynomial ℚ)
    (Mzk1G1ProjectiveLineTransitionActual.evalAt (R := Polynomial ℚ) h)
    (by exact RingHom.ext_rat _ _) Polynomial.X]
  congr 1
  simp [Mzk1G1ProjectiveLineTransitionActual.evalAt]

/-- Lambda-chart formula: `lambda' = h(lambda)`. -/
theorem hPolyL_lambda_chart (h : Polynomial ℚ) (hh : h ≠ 0) :
    localChart0 ≫ hPolyL h hh = chartMorphism0 (R := Polynomial ℚ) h := by
  rw [hPolyL_def, ← Category.assoc, ← Category.assoc]
  rw [show localChart0 ≫ p1Inv = chartMorphismInf (R := Polynomial ℚ) Polynomial.X from
    p1Inv_ι_false]
  rw [chartMorphismInf_X_comp_hPoly h hh, chartMorphismInf_comp_p1Inv h]

/-- The composite `phiFixedL = psiFixed ≫ hPolyL` (the B1 morphism). -/
noncomputable def phiFixedL (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) :
    fermatCurveScheme n ⟶ projectiveLineGlued :=
  psiFixed n T ≫ hPolyL h hh

#print axioms evalAt_X_self
#print axioms chartMorphismInf_X_comp_hPoly
#print axioms chartMorphismInf_comp_p1Inv
#print axioms hPolyL_lambda_chart
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual