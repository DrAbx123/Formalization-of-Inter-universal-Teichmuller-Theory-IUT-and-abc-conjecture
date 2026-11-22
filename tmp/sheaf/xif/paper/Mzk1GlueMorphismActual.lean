import tmp.sheaf.xif.paper.Mzk1HullFermatGluingActual
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1GlueMorphismActual
open LeanFormal.IUT.XiFPaper.Mzk1HullFermatGluingActual

variable {D : Scheme.GlueData} {Z : Scheme}

/-- The pullback-level compatibility of chart morphisms, deduced from the overlap-level
compatibility: D.f i j composed with f i equals D.t i j composed with D.f j i and f j. -/
theorem glueMorphisms_compat (f : ∀ i : D.J, D.U i ⟶ Z)
    (h : ∀ i j, D.f i j ≫ f i = D.t i j ≫ D.f j i ≫ f j) :
    ∀ i j, pullback.fst (D.ι i) (D.ι j) ≫ f i =
      pullback.snd (D.ι i) (D.ι j) ≫ f j := by
  intro i j
  let l : pullback (D.ι i) (D.ι j) ⟶ D.V (i, j) :=
    PullbackCone.IsLimit.lift (D.vPullbackConeIsLimit i j)
      (pullback.fst (D.ι i) (D.ι j)) (pullback.snd (D.ι i) (D.ι j)) pullback.condition
  have hl1 : l ≫ D.f i j = pullback.fst (D.ι i) (D.ι j) :=
    PullbackCone.IsLimit.lift_fst (D.vPullbackConeIsLimit i j) _ _ _
  have hl2 : l ≫ (D.t i j ≫ D.f j i) = pullback.snd (D.ι i) (D.ι j) :=
    PullbackCone.IsLimit.lift_snd (D.vPullbackConeIsLimit i j) _ _ _
  rw [← hl1, ← hl2]
  simp only [Category.assoc]
  exact congrArg (fun m => l ≫ m) (h i j)

/-- GLUE-MORPHISMS OUT OF A GLUED SCHEME: compatible chart morphisms glue to a
morphism out of D.glued. -/
noncomputable def glueMorphism (f : ∀ i : D.J, D.U i ⟶ Z)
    (h : ∀ i j, D.f i j ≫ f i = D.t i j ≫ D.f j i ≫ f j) : D.glued ⟶ Z :=
  D.openCover.glueMorphisms f (glueMorphisms_compat f h)

/-- The restriction of the glued morphism to each chart. -/
theorem glueMorphism_ι (f : ∀ i : D.J, D.U i ⟶ Z)
    (h : ∀ i j, D.f i j ≫ f i = D.t i j ≫ D.f j i ≫ f j) (i : D.J) :
    D.ι i ≫ glueMorphism f h = f i :=
  D.openCover.ι_glueMorphisms f (glueMorphisms_compat f h) i

#print axioms glueMorphisms_compat
#print axioms glueMorphism
#print axioms glueMorphism_ι
end LeanFormal.IUT.XiFPaper.Mzk1GlueMorphismActual
