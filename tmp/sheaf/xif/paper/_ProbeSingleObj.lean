import Iut.Foundations.Orbicurve
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
open CategoryTheory
open CategoryTheory.Bicategory
namespace Test
noncomputable section
example (f : (Quiver.SingleObj.star Iut.SignGroup : CategoryTheory.SingleObj Iut.SignGroup) ⟶ Quiver.SingleObj.star Iut.SignGroup) : True := by
  letI : Category (CategoryTheory.SingleObj Iut.SignGroup) := CategoryTheory.SingleObj.category
  have h : f = 1 := by rfl
  trivial
#check CategoryTheory.SingleObj.comp_as_mul
#check CategoryTheory.SingleObj.id_as_one
end
end Test
