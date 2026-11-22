import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

open CategoryTheory CategoryTheory.Limits

example : AddGroupWithOne ℚ := inferInstance
example : PreservesLimitsOfShape WalkingCospan (forget AddCommGrpCat.{0}) := inferInstance
example : Mono (AddCommGrpCat.ofHom (Int.castAddHom ℚ)) := by
  rw [ConcreteCategory.mono_iff_injective_of_preservesPullback]
  exact Int.cast_injective
