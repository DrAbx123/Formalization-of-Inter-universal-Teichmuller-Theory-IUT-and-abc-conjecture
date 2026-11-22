/- B1: scheme-level value dictionary ingredients for the glued P¹ (no ℂ downgrade).

  The remaining dictionary needs (per emmy's Mzk1G1PsiM2BranchDataActual header):
  (i) the t-chart dictionary and (ii) `Branch (hPolyL h hh) = critical values of h ∪ {∞}`.
  This file supplies the scheme-level point-action form of henry's lambda-chart formula
  `hPolyL_lambda_chart : localChart0 ≫ hPolyL h hh = chartMorphism0 (R := ℚ[λ]) h`, which is
  exactly the `val_hPolyL` ingredient of `P1ValueDictionary` expressed on points rather than
  on ℂ-valued coordinates. No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1P1DictActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual

/-- **`hPolyL` 在 chart-0 点上的作用**（scheme 级 value 形式）：
    `hPolyL h hh (localChart0 x) = chartMorphism0 h x`。 -/
theorem hPolyL_localChart0_apply (h : Polynomial ℚ) (hh : h ≠ 0)
    (x : Spec (CommRingCat.of (Polynomial ℚ))) :
    hPolyL h hh (localChart0 x) = chartMorphism0 h x := by
  have hc := congrArg (fun g => g x) (hPolyL_lambda_chart h hh)
  simpa [Scheme.Hom.comp_apply] using hc

#print axioms hPolyL_localChart0_apply

end LeanFormal.IUT.XiFPaper.Mzk1G1B1P1DictActual