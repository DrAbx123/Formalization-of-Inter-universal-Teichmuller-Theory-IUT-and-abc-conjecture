import tmp.sheaf.xif.paper.S2854SignQuotientAux
import tmp.sheaf.xif.paper.S1971ActionStackificationActual
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2872PointwiseQuotientPseudofunctorActual
open Iut
open LeanFormal.IUT.XiFPaper.S2854SignQuotientAux
variable {F : Type u} [Field F]
variable (xF : Iut.HyperbolicOrbicurve F)
variable (signAction : Iut.OrbicurveSignAction xF)

/-- Pointwise quotient fiber, conditional on the missing sign action on the
fiber objects. -/
noncomputable def S2872PointwiseQuotient
    (h : ∀ U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ,
      MulAction Iut.SignGroup ↑(xF.stack.fiber.obj U))
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) : Cat :=
  letI := h U
  Cat.of (ActionCategory Iut.SignGroup (xF.stack.fiber.obj U))

/-- obj/map/mapId/mapComp skeleton of the pointwise-quotient pseudofunctor.
No IsStack and no coherence are asserted. -/
structure S2872PointwiseQuotientPseudofunctorData where
  obj : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ → Cat
  map : ∀ {U V : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ}, (U ⟶ V) → (obj U ⟶ obj V)
  mapId : ∀ U, map (𝟙 U) ≅ 𝟙 (obj U)
  mapComp : ∀ {U V W} (f : U ⟶ V) (g : V ⟶ W),
    map (f ≫ g) ≅ map f ≫ map g

/-- The actual target of W, over the generic xF/signAction. -/
abbrev S2872StackQuotientInput : Type _ := S2854StackQuotientInput xF signAction

#check S2872PointwiseQuotient
#check S2872PointwiseQuotientPseudofunctorData
#check S2872StackQuotientInput

end LeanFormal.IUT.XiFPaper.S2872PointwiseQuotientPseudofunctorActual