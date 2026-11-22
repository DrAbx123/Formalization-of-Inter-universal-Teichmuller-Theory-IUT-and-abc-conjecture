import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

open CategoryTheory
open CategoryTheory.Limits

universe u v w
variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
variable {ι : Type w} [Fintype ι] (comp : ι → C) (c : Cofan comp) (hc : IsColimit c)

#check @IsColimit.desc
#check @Cofan.IsColimit.desc
#check @Cofan.IsColimit.fac
#check @Cofan.IsColimit.inj_desc
#check @Cofan.IsColimit.hom_ext
#check @Cofan.mk
#check @Cofan.inj
#check @Sigma.ι
#check @Sigma.hom_ext
