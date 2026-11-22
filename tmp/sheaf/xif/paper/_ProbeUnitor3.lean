import Iut.Foundations.Orbicurve
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
namespace T
universe u
variable {F : Type u} [Field F]
variable (X : Iut.HyperbolicOrbicurve F)
example :
    (𝟙 X.stack.fiber : X.stack.fiber ⟶ X.stack.fiber) ≅
      (𝟙 X.stack.fiber : X.stack.fiber ⟶ X.stack.fiber) ≫
        𝟙 X.stack.fiber :=
  ⟨(λ_ (𝟙 X.stack.fiber)).symm⟩
example (inv : X.Hom X) :
    inv ≅ (𝟙 X.stack.fiber : X.stack.fiber ⟶ X.stack.fiber) ≫ inv :=
  ⟨(λ_ (show X.stack.fiber ⟶ X.stack.fiber from inv)).symm⟩
end T
