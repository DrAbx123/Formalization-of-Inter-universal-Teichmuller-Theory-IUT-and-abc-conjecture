import Iut.Foundations.Orbicurve
noncomputable section
open CategoryTheory
namespace LeanFormal.IUT.XiFPaper.OrbicurveEtaleFundamentalGroupAssemblyAttempt
universe u
variable {F : Type u} [Field F]
variable {X : Iut.HyperbolicOrbicurve F}
variable {group : ProfiniteGrp.{u}}

/-- Conditional assembly of `OrbicurveEtaleFundamentalGroup` with every field
explicit (the constructor arguments): coverCategory, galoisCategory,
baseScheme, basePoint, fiber, fiberFunctor, coverMorphism,
coverMorphism_over, coverMorphism_bijective, coverMorphism_id,
coverMorphism_comp, geometricFiberFintype, fiberIdentification,
fiberIdentification_natural, action, isFundamentalGroup. -/
noncomputable def assembly :=
  @Iut.OrbicurveEtaleFundamentalGroup.mk F _ X group

#check assembly

end LeanFormal.IUT.XiFPaper.OrbicurveEtaleFundamentalGroupAssemblyAttempt