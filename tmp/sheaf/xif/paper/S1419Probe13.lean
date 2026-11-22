import tmp.sheaf.n8.closure.DiscreteSheafIsStack
import Mathlib.CategoryTheory.Sites.Sheaf

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack

namespace S1419Probe13

universe v u

variable {C : Type u} [Category.{v} C]

variable (P : Cᵒᵖ ⥤ Type v) {X : C} (S : Sieve X)

theorem full (hS : Presieve.IsSheafFor P S.arrows) :
    ((discretePseudo P).toDescentData
      (fun i : S.arrows.category => i.obj.hom)).Full where
  map_surjective {x₁ x₂} φ := by
    have hx : x₁.as = x₂.as := by
      apply (hS.isSeparatedFor).ext
      intro Y f hf
      let i : S.arrows.category := ⟨Over.mk f, hf⟩
      have h := Discrete.eq_of_hom (φ.hom i)
      change P.map f.op x₁.as = P.map f.op x₂.as at h
      exact h
    refine ⟨Discrete.eqToHom hx, ?_⟩
    haveI : Subsingleton
        (((discretePseudo P).toDescentData (fun i : S.arrows.category => i.obj.hom)).obj x₁ ⟶
          ((discretePseudo P).toDescentData (fun i : S.arrows.category => i.obj.hom)).obj x₂) := by
      constructor
      intro f g
      apply Pseudofunctor.DescentData.hom_ext
      intro i
      exact @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _
    exact Subsingleton.elim _ _

end S1419Probe13

end
