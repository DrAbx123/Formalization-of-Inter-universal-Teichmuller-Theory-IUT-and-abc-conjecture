/- `chartMorphism0 a` followed by the P^1 inversion is `chartMorphismInf a`. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiP1InvActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyFinalActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineGluedActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineTransitionActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaTActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual

theorem chartMorphism0_comp_p1Inv {R : Type} [CommRing R] [Algebra ℚ R] (a : R) :
    chartMorphism0 (R := R) a ≫ p1Inv = chartMorphismInf (R := R) a := by
  show Spec.map (CommRingCat.ofHom (Mzk1G1ProjectiveLineTransitionActual.evalAt
      (R := R) a)) ≫ localChart0 ≫ p1Inv = _
  rw [show localChart0 ≫ p1Inv = chartMorphismInf (R := Polynomial ℚ) Polynomial.X from
    p1Inv_ι_false]
  rw [specMap_chartMorphismInf (R := Polynomial ℚ) (S := R)
    (Mzk1G1ProjectiveLineTransitionActual.evalAt (R := R) a) (by exact RingHom.ext_rat _ _)
    Polynomial.X]
  congr 1
  simp [Mzk1G1ProjectiveLineTransitionActual.evalAt]

#print axioms chartMorphism0_comp_p1Inv
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaTActual