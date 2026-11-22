import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.ZMod.Basic

open CategoryTheory
open scoped Bicategory

set_option autoImplicit false

namespace Probe2436

abbrev X : AddCommGrpCat.{0} := AddCommGrpCat.of ℤ
abbrev S : AddCommGrpCat.{0} := AddCommGrpCat.of ℚ
abbrev T : AddCommGrpCat.{0} := AddCommGrpCat.of (ZMod 2)

noncomputable def f : X ⟶ S := AddCommGrpCat.ofHom (Int.castAddHom ℚ)

example : f ≫ AddCommGrpCat.ofHom (0 : ℚ →+ ZMod 2) = AddCommGrpCat.ofHom (0 : ℤ →+ ZMod 2) := by
  change AddCommGrpCat.ofHom (Int.castAddHom ℚ) ≫ AddCommGrpCat.ofHom (0 : ℚ →+ ZMod 2) =
    AddCommGrpCat.ofHom (0 : ℤ →+ ZMod 2)
  rw [← AddCommGrpCat.ofHom_comp]
  simp

end Probe2436
