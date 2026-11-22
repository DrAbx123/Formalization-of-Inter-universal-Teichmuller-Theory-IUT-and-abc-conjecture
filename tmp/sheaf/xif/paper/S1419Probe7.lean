import tmp.sheaf.n8.closure.DiscreteSheafIsStack
import Mathlib.CategoryTheory.Sites.Sheaf

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack

namespace S1419Probe7

universe v u

variable {C : Type u} [Category.{v} C]

variable (P : Cᵒᵖ ⥤ Type v) {X : C} (S : Sieve X)
  (D : (discretePseudo P).DescentData (fun i : S.arrows.category => i.obj.hom))

example (Y Z : C) (u : Y ⟶ X) (g : Z ⟶ Y) (hu : S.arrows u) : True := by
  let i₁ : S.arrows.category := ⟨Over.mk u, hu⟩
  let i₂ : S.arrows.category := ⟨Over.mk (g ≫ u), S.downward_closed hu g⟩
  have hD := D.hom (Y := Z) (q := g ≫ u) (i₁ := i₁) (i₂ := i₂)
    (f₁ := g) (f₂ := 𝟙 Z) (by rfl) (by rw [id_comp])
  have hEq := Discrete.eq_of_hom hD
  trivial

end S1419Probe7

end
