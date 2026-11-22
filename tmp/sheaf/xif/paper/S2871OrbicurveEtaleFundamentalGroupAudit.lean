import Iut.Foundations.Orbicurve

noncomputable section
open CategoryTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace S2871OrbicurveEtaleFundamentalGroupAudit

universe u

/-!
# Audit: `Iut.OrbicurveEtaleFundamentalGroup`

The structure has exactly the following 16 fields, and NO producer/constructor
from arithmetic data is available in the tree:

1. coverCategory : Category (OrbicurveFiniteEtaleCover X)
2. galoisCategory : GaloisCategory (OrbicurveFiniteEtaleCover X)
3. baseScheme : SchemeOverField F
4. basePoint : StrongTrans (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber
5. fiber : OrbicurveFiniteEtaleCover X ⥤ FintypeCat
6. fiberFunctor : PreGaloisCategory.FiberFunctor fiber
7. coverMorphism : source ⟶ target → source.source.Hom target.source
8. coverMorphism_over : Iso (vcomp (coverMorphism map) target.map) source.map
9. coverMorphism_bijective : Bijective coverMorphism
10. coverMorphism_id : Iso (coverMorphism 𝟙) id
11. coverMorphism_comp : Iso (coverMorphism (f ≫ g)) (vcomp ...)
12. geometricFiberFintype
13. fiberIdentification
14. fiberIdentification_natural
15. action : MulAction group (fiber.obj cover)
16. isFundamentalGroup : IsFundamentalGroup fiber group

Only the anonymous `mk` and the projections exist; `mk` is not a construction
from `A`/`scheaf` data. The only consumer-facing constructor in the tree is
`Iut.SourceOrbicurveGroupData.ofFundamentalGroup`, which TAKES both the
arithmetic and geometric `OrbicurveEtaleFundamentalGroup` terms as inputs.
-/

#check Iut.OrbicurveEtaleFundamentalGroup
#check Iut.OrbicurveEtaleFundamentalGroup.mk
#check @Iut.OrbicurveEtaleFundamentalGroup.coverCategory
#check @Iut.OrbicurveEtaleFundamentalGroup.galoisCategory
#check @Iut.OrbicurveEtaleFundamentalGroup.baseScheme
#check @Iut.OrbicurveEtaleFundamentalGroup.basePoint
#check @Iut.OrbicurveEtaleFundamentalGroup.fiber
#check @Iut.OrbicurveEtaleFundamentalGroup.fiberFunctor
#check @Iut.OrbicurveEtaleFundamentalGroup.coverMorphism
#check @Iut.OrbicurveEtaleFundamentalGroup.coverMorphism_over
#check @Iut.OrbicurveEtaleFundamentalGroup.coverMorphism_bijective
#check @Iut.OrbicurveEtaleFundamentalGroup.coverMorphism_id
#check @Iut.OrbicurveEtaleFundamentalGroup.coverMorphism_comp
#check @Iut.OrbicurveEtaleFundamentalGroup.geometricFiberFintype
#check @Iut.OrbicurveEtaleFundamentalGroup.fiberIdentification
#check @Iut.OrbicurveEtaleFundamentalGroup.fiberIdentification_natural
#check @Iut.OrbicurveEtaleFundamentalGroup.action
#check @Iut.OrbicurveEtaleFundamentalGroup.isFundamentalGroup
#check Iut.OrbicurveEtaleFundamentalGroup.toEtaleFundamentalGroup
#check Iut.OrbicurveEtaleFundamentalGroup.group

/-- The exact constructor gap: inhabitation of the structure. -/
def ConstructorGap {F : Type u} [Field F]
    (X : Iut.HyperbolicOrbicurve F) (group : ProfiniteGrp.{u}) : Prop :=
  Nonempty (Iut.OrbicurveEtaleFundamentalGroup X group)

theorem constructorGap_iff {F : Type u} [Field F]
    (X : Iut.HyperbolicOrbicurve F) (group : ProfiniteGrp.{u}) :
    ConstructorGap X group ↔
      Nonempty (Iut.OrbicurveEtaleFundamentalGroup X group) :=
  Iff.rfl

#check ConstructorGap
#check constructorGap_iff
#print axioms constructorGap_iff

end S2871OrbicurveEtaleFundamentalGroupAudit
end
