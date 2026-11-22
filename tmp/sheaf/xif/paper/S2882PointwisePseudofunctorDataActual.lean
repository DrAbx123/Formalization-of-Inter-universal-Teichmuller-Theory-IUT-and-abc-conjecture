import tmp.sheaf.xif.paper.S1971ActionStackificationActual
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2882PointwisePseudofunctorDataActual
open Iut
variable {F : Type u} [Field F]

/-- Manual pseudofunctor data for the pointwise quotient: obj/map/mapId/mapComp
plus the three coherence fields, with no Grothendieck/2-colimit API. -/
structure S2882PointwisePseudofunctorData where
  obj : (Iut.SchemeOverField F)ᵒᵖ → Cat
  map : ∀ {U V : (Iut.SchemeOverField F)ᵒᵖ}, (U ⟶ V) → (obj U ⟶ obj V)
  mapId : ∀ U, map (𝟙 U) ≅ 𝟙 (obj U)
  mapComp : ∀ {U V W} (f : U ⟶ V) (g : V ⟶ W),
    map (f ≫ g) ≅ map f ≫ map g
  map₂_associator : ∀ {a b c d : (Iut.SchemeOverField F)ᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
    (mapComp (f ≫ g) h).hom ≫
      (mapComp f g).hom ▷ map h ≫
      (α_ (map f) (map g) (map h)).hom ≫
      map f ◁ (mapComp g h).inv ≫ (mapComp f (g ≫ h)).inv = eqToHom (by simp)
  map₂_left_unitor : ∀ {a b : (Iut.SchemeOverField F)ᵒᵖ} (f : a ⟶ b),
    (mapComp (𝟙 a) f).hom ≫ (mapId a).hom ▷ map f ≫ (λ_ (map f)).hom = eqToHom (by simp)
  map₂_right_unitor : ∀ {a b : (Iut.SchemeOverField F)ᵒᵖ} (f : a ⟶ b),
    (mapComp f (𝟙 b)).hom ≫ map f ◁ (mapId b).hom ≫ (ρ_ (map f)).hom = eqToHom (by simp)

noncomputable def S2882PseudofunctorOfData
    (D : S2882PointwisePseudofunctorData (F := F)) :
    Iut.EtaleStackPseudofunctor F :=
  LocallyDiscrete.mkPseudofunctor D.obj D.map D.mapId D.mapComp
    D.map₂_associator D.map₂_left_unitor D.map₂_right_unitor

#check S2882PointwisePseudofunctorData
#check S2882PseudofunctorOfData

end LeanFormal.IUT.XiFPaper.S2882PointwisePseudofunctorDataActual