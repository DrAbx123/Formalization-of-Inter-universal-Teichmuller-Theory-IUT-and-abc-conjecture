import tmp.sheaf.n8.closure.DiscreteSheafIsStack
import Mathlib.CategoryTheory.Sites.Sheaf

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack

namespace S1419Probe11

universe v u

variable {C : Type u} [Category.{v} C]

variable (P : Cᵒᵖ ⥤ Type v) {X : C} (S : Sieve X)

example {D₁ D₂ : (discretePseudo P).DescentData (fun i : S.arrows.category => i.obj.hom)}
    (φ : D₁ ⟶ D₂) : D₁ = D₂ := by
  have hobj : D₁.obj = D₂.obj := funext (fun i => by
    have h := Discrete.eq_of_hom (φ.hom i)
    rw [← Discrete.mk_as (D₁.obj i), ← Discrete.mk_as (D₂.obj i)]
    exact congrArg Discrete.mk h)
  cases D₁ with
  | mk obj₁ hom₁ pull₁ self₁ comp₁ =>
    cases D₂ with
    | mk obj₂ hom₂ pull₂ self₂ comp₂ =>
      dsimp only at hobj
      subst hobj
      have hhom : hom₂ = hom₁ := by
        funext Y q i₁ i₂ f₁ f₂ hf₁ hf₂
        exact @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _
      subst hhom
      congr 1 <;> exact Subsingleton.elim _ _

end S1419Probe11

end
