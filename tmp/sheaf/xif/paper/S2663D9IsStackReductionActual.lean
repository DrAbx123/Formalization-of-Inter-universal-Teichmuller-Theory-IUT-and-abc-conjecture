import Mathlib.CategoryTheory.Sites.Descent.IsStack

noncomputable section
open CategoryTheory
open scoped CategoryTheory.Bicategory

namespace LeanFormal.IUT.XiFPaper.S2663D9IsStackReductionActual

universe v u v₁ u₁
variable {C : Type u} [Category.{v} C]
variable (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v₁, u₁}) (J : GrothendieckTopology C)

/-- `IsStack` is exactly `IsPrestack` plus effectivity (`EssSurj`) for all
covering sieves. This is the exact reduction of the D9 target to its two
remaining fields. -/
theorem S2663IsStack_iff :
    F.IsStack J ↔
      F.IsPrestack J ∧
        ∀ {S : C} (R : Sieve S) (hR : R ∈ J S),
          (F.toDescentData (fun (f : R.arrows.category) => f.obj.hom)).EssSurj := by
  constructor
  · intro h
    exact ⟨h.toIsPrestack, fun R hR => h.essSurj_of_sieve R hR⟩
  · rintro ⟨hp, he⟩
    exact {
      toIsPrestack := hp
      essSurj_of_sieve := fun R hR => he R hR }

#print axioms S2663IsStack_iff

end LeanFormal.IUT.XiFPaper.S2663D9IsStackReductionActual
end