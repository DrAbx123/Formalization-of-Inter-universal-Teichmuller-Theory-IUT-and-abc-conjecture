import tmp.sheaf.n8.closure.DiscreteSheafIsStack
import Mathlib.CategoryTheory.Sites.Sheaf

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack

namespace S1419Probe5

universe v u

variable {C : Type u} [Category.{v} C]

noncomputable def fam (P : Cᵒᵖ ⥤ Type v) {X : C} (S : Sieve X)
    (D : (discretePseudo P).DescentData (fun i : S.arrows.category => i.obj.hom)) :
    Presieve.FamilyOfElements P S.arrows :=
  fun _ f hf => (D.obj ⟨Over.mk f, hf⟩).as

variable (P : Cᵒᵖ ⥤ Type v) {X : C} (S : Sieve X)
  (D : (discretePseudo P).DescentData (fun i : S.arrows.category => i.obj.hom))

example (Y Z : C) (u : Y ⟶ X) (g : Z ⟶ Y) (hu : S.arrows u) :
    fam P S D (g ≫ u) (S.downward_closed hu g) = P.map g.op (fam P S D u hu) := by
  let i₁ : S.arrows.category := ⟨Over.mk u, hu⟩
  let i₂ : S.arrows.category := ⟨Over.mk (g ≫ u), S.downward_closed hu g⟩
  have hD := D.hom (Y := Z) (q := g ≫ u) (i₁ := i₁) (i₂ := i₂)
    (f₁ := g) (f₂ := 𝟙 Z) (by rfl) (by simp)
  have hEq := Discrete.eq_of_hom hD
  rw [show ((discretePseudo P).map (Quiver.Hom.toLoc g.op)).toFunctor.obj (D.obj i₁) =
      Discrete.mk (P.map g.op (D.obj i₁).as) from rfl,
    show ((discretePseudo P).map (Quiver.Hom.toLoc (𝟙 Z).op)).toFunctor.obj (D.obj i₂) =
      Discrete.mk (P.map (𝟙 Z).op (D.obj i₂).as) from rfl] at hEq
  simp only [Discrete.mk_as] at hEq
  rw [show P.map (𝟙 Z).op (D.obj i₂).as = (D.obj i₂).as by simp] at hEq
  exact hEq.symm

end S1419Probe5

end
