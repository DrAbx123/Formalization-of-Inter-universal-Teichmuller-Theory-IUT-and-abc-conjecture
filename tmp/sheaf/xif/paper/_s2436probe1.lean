import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.ConcreteCategory.Basic

open CategoryTheory
open scoped Bicategory

#check AddCommGrpCat
#check AddCommGrpCat.of
#check AddCommGrpCat.ofHom
#check Int.castAddHom
#check AddCommGrpCat.mono_iff_injective
#check ConcreteCategory.mono_iff_injective
#check CategoryTheory.Cat.of
#check Discrete.functor
#check CategoryTheory.Functor.toPseudofunctor'
#check CategoryTheory.LocallyDiscrete.mkPseudofunctor
#check Pseudofunctor.toDescentData
#check Functor.EssSurj
#check Int.cast_injective

example : Mono (AddCommGrpCat.ofHom (Int.castAddHom ℚ)) := by
  rw [AddCommGrpCat.mono_iff_injective]
  exact Int.cast_injective
