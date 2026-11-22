import tmp.sheaf.xif.paper.S2854SignQuotientAux
import tmp.sheaf.xif.paper.S1971ActionStackificationActual
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2872GenericStackQuotientActual
open Iut
open LeanFormal.IUT.XiFPaper.S2854SignQuotientAux
variable {F : Type u} [Field F]
variable (xF : Iut.HyperbolicOrbicurve F)
variable (signAction : Iut.OrbicurveSignAction xF)

/-- Generic skeleton of the functorial pointwise colimit: only the
pseudofunctor fields are recorded; coherence is explicit. -/
structure S2872FunctorialPointwiseColimitSkeleton where
  obj : (LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) → Cat
  map : ∀ {U V : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ}, (U ⟶ V) → (obj U ⟶ obj V)
  mapId : ∀ U, map (𝟙 U) ≅ 𝟙 (obj U)
  mapComp : ∀ {U V W} (f : U ⟶ V) (g : V ⟶ W),
    map (f ≫ g) ≅ map f ≫ map g

abbrev S2872StackQuotientInput : Type _ := S2854StackQuotientInput xF signAction

#check S2872FunctorialPointwiseColimitSkeleton
#check S2872StackQuotientInput

end LeanFormal.IUT.XiFPaper.S2872GenericStackQuotientActual