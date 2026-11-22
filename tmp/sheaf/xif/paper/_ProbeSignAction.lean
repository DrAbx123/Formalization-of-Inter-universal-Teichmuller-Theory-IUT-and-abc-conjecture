import Iut.Foundations.Orbicurve
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
namespace Iut
noncomputable section
universe u
variable {F : Type u} [Field F]
variable (X : HyperbolicOrbicurve F)
variable (inv : X.Hom X)
variable (invSq : HyperbolicOrbicurve.Hom.TwoIso (HyperbolicOrbicurve.Hom.comp inv inv) (HyperbolicOrbicurve.Hom.id X))
def mapHom (g : SignGroup) : X.stack.fiber ⟶ X.stack.fiber :=
  if g = 1 then HyperbolicOrbicurve.Hom.id X else inv
example : mapHom X inv 1 = HyperbolicOrbicurve.Hom.id X := by simp [mapHom]
example : mapHom X inv (Multiplicative.ofAdd (1 : ZMod 2)) = inv := by
  simp [mapHom]
  intro h
  have h1 : (Multiplicative.ofAdd (1 : ZMod 2)) = 1 := h
  -- contradiction via additive
  have := congrArg Multiplicative.toAdd h1
  simpa using this
