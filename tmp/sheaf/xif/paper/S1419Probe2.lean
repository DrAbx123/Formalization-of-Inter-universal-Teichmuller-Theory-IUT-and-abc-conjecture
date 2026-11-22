import tmp.sheaf.n8.closure.DiscreteSheafIsStack
import Mathlib.CategoryTheory.Sites.Sheaf

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack

namespace S1419Probe2

universe v u

variable {C : Type u} [Category.{v} C]

/-- The compatible family associated to a descent datum of the discrete
pseudofunctor of a presheaf `P`. -/
noncomputable def fam (P : Cᵒᵖ ⥤ Type v) {X : C} (S : Sieve X)
    (D : (discretePseudo P).DescentData (fun i : S.arrows.category => i.obj.hom)) :
    Presieve.FamilyOfElements P S.arrows :=
  fun Y f hf => (D.obj ⟨Over.mk f, hf⟩).as

variable (P : Cᵒᵖ ⥤ Type v) {X : C} (S : Sieve X)

example (D : (discretePseudo P).DescentData (fun i : S.arrows.category => i.obj.hom)) :
    (fun Y f hf => (D.obj ⟨Over.mk f, hf⟩).as) = fam P S D := rfl

end S1419Probe2

end
