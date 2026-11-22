import tmp.sheaf.xif.paper.S2070CurveEtaleFundamentalCardActual
import tmp.sheaf.xif.paper.S2081CurveCardM2Actual

noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
universe u w w'

#print TypeCat
#check @TypeCat.ofHom
#check @TypeCat.Fun
#check @CategoryTheory.ConcreteCategory.hom_ext
#check @CategoryTheory.Functor.map_injective
#check @TypeCat.hom_ext

namespace TransferTest

theorem preservesLimitsOfShape_of_comp_of_reflects {C : Type*} [Category C] {D : Type*} [Category D]
    {E : Type*} [Category E] {J : Type*} [Category J] (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsLimitsOfShape J G] [PreservesLimitsOfShape J (F ⋙ G)] :
    PreservesLimitsOfShape J F where
  preservesLimit {K} :=
    { preserves := fun {c} hc => by
        have h1 : IsLimit ((F ⋙ G).mapCone c) := isLimitOfPreserves (F ⋙ G) hc
        exact ReflectsLimit.reflects (K := K) (F := G) (c := F.mapCone c) h1 }

theorem preservesColimitsOfShape_of_comp_of_reflects {C : Type*} [Category C] {D : Type*} [Category D]
    {E : Type*} [Category E] {J : Type*} [Category J] (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsColimitsOfShape J G] [PreservesColimitsOfShape J (F ⋙ G)] :
    PreservesColimitsOfShape J F where
  preservesColimit {K} :=
    { preserves := fun {c} hc => by
        have h1 : IsColimit ((F ⋙ G).mapCocone c) := isColimitOfPreserves (F ⋙ G) hc
        exact ReflectsColimit.reflects (K := K) (F := G) (c := F.mapCocone c) h1 }

instance reflectsEpimorphisms_fintypeCatIncl : Functor.ReflectsEpimorphisms FintypeCat.incl where
  reflects {X Y} f hf := by
    rw [epi_iff_epi_map] at *
    sorry

end TransferTest
