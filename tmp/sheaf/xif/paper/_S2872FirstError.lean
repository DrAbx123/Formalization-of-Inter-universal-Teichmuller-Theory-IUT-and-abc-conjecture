import tmp.sheaf.xif.paper.S2872GenericStackQuotientActual
open CategoryTheory
open LeanFormal.IUT
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2872FirstError
variable {F : Type u} [Field F]
variable (xF : Iut.HyperbolicOrbicurve F)
noncomputable def S2872PointwiseQuotient
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) : Cat :=
  Cat.of (ActionCategory Iut.SignGroup (xF.stack.fiber.obj U))
end LeanFormal.IUT.XiFPaper.S2872FirstError