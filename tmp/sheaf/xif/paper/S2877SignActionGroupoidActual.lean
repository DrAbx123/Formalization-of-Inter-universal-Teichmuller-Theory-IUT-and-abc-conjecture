import Iut.Foundations.Orbicurve
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2877SignActionGroupoidActual
open Iut
variable {F : Type u} [Field F]
variable (xF : Iut.HyperbolicOrbicurve F)
variable (signAction : Iut.OrbicurveSignAction xF)

noncomputable def S2877SignFunctor
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) :
    xF.stack.fiber.obj U ⥤ xF.stack.fiber.obj U :=
  (signAction.inversion.app U).toFunctor

def S2877SignSquareIso (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) : Prop :=
  Nonempty (S2877SignFunctor xF signAction U ⋙
    S2877SignFunctor xF signAction U ≅ 𝟭 (xF.stack.fiber.obj U))

structure S2877SignActionGroupoidData
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) where
  sign : xF.stack.fiber.obj U ⥤ xF.stack.fiber.obj U
  sign_eq : sign = S2877SignFunctor xF signAction U
  squareIso : Nonempty (sign ⋙ sign ≅ 𝟭 (xF.stack.fiber.obj U))

def S2877MissingTwoColimitAPI : Prop :=
  ∃ G : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ → Type u,
    ∀ U, Nonempty (G U)

#check S2877SignFunctor
#check S2877SignSquareIso
#check S2877SignActionGroupoidData
#check S2877MissingTwoColimitAPI

end LeanFormal.IUT.XiFPaper.S2877SignActionGroupoidActual