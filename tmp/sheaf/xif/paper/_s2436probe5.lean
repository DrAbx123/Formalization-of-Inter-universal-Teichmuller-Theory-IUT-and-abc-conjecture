import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.ZMod.Basic

open CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace Probe2436

abbrev X : AddCommGrpCat.{0} := AddCommGrpCat.of ℤ
abbrev S : AddCommGrpCat.{0} := AddCommGrpCat.of ℚ
abbrev T : AddCommGrpCat.{0} := AddCommGrpCat.of (ZMod 2)

noncomputable def f : X ⟶ S := AddCommGrpCat.ofHom (Int.castAddHom ℚ)
noncomputable def m : X ⟶ T := AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2))

#check cancel_mono
#check Mono.right_cancellation

instance : Mono f := by
  constructor
  intro Z g₁ g₂ h
  rw [← AddCommGrpCat.ofHom_hom g₁, ← AddCommGrpCat.ofHom_hom g₂]
  congr 1
  apply AddMonoidHom.ext
  intro x
  have hx := congrFun (congrArg (fun (k : Z ⟶ S) => (k : Z → ℚ)) h) x
  simp only [ConcreteCategory.comp_apply] at hx
  exact Int.cast_injective hx

end Probe2436
