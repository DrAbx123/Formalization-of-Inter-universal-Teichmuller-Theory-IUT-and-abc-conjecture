import Iut.Foundations.Orbicurve
open CategoryTheory
open CategoryTheory.Bicategory
namespace T
universe u
variable {F : Type u} [Field F]
variable (X : Iut.HyperbolicOrbicurve F)
example : (Iut.HyperbolicOrbicurve.Hom.id X : X.stack.fiber ⟶ X.stack.fiber) =
    𝟙 X.stack.fiber := rfl
example : (Iut.HyperbolicOrbicurve.Hom.id X : X.stack.fiber ⟶ X.stack.fiber) =
    𝟙 X.stack.fiber := by rfl
end T
