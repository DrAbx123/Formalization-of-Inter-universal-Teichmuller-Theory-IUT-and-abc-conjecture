import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.ZMod.Basic

open CategoryTheory

#check Functor.EssSurj
#check Functor.EssSurj.essImage
#check Functor.essImage
#check Functor.mem_essImage
#synth Zero (AddCommGrpCat.of (ℚ) ⟶ AddCommGrpCat.of (ZMod 2))
#synth Preadditive AddCommGrpCat
#check nsmul_eq_mul
#check map_nsmul
#check two_nsmul
