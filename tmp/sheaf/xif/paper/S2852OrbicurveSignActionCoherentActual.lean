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

/-- A coherent diagram from explicit pseudofunctor data. -/
def signActionDiagramOf
    (obj : SingleObj SignGroup → EtaleStackPseudofunctor F)
    (map : ∀ {b b' : SingleObj SignGroup}, (b ⟶ b') → (obj b ⟶ obj b'))
    (mapId : ∀ b : SingleObj SignGroup, map (𝟙 b) ≅ 𝟙 (obj b))
    (mapComp : ∀ {b₀ b₁ b₂ : SingleObj SignGroup}
      (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂), map (f ≫ g) ≅ map f ≫ map g)
    (map₂_associator : ∀ {b₀ b₁ b₂ b₃ : SingleObj SignGroup}
      (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃),
      (mapComp (f ≫ g) h).hom ≫
        (mapComp f g).hom ▷ map h ≫
        (α_ (map f) (map g) (map h)).hom ≫
        map f ◁ (mapComp g h).inv ≫
        (mapComp f (g ≫ h)).inv = eqToHom (by simp))
    (map₂_left_unitor : ∀ {b₀ b₁ : SingleObj SignGroup} (f : b₀ ⟶ b₁),
      (mapComp (𝟙 b₀) f).hom ≫
        (mapId b₀).hom ▷ map f ≫
        (λ_ (map f)).hom = eqToHom (by simp))
    (map₂_right_unitor : ∀ {b₀ b₁ : SingleObj SignGroup} (f : b₀ ⟶ b₁),
      (mapComp f (𝟙 b₁)).hom ≫
        map f ◁ (mapId b₁).hom ≫
        (ρ_ (map f)).hom = eqToHom (by simp)) :
    SignActionIndex ⥤ᵖ EtaleStackPseudofunctor F :=
  LocallyDiscrete.mkPseudofunctor obj map mapId mapComp
    map₂_associator map₂_left_unitor map₂_right_unitor

/-- Build an OrbicurveSignAction from a coherent diagram and the remaining
sign data.  This is the exact interface left by the coherence blocker. -/
noncomputable def orbicurveSignActionOf
    (D : SignActionIndex ⥤ᵖ EtaleStackPseudofunctor F)
    (atBase : Bicategory.Equivalence (D.obj signActionObject) X.stack.fiber)
    (inversion : X.Hom X)
    (generator_identification :
      (atBase.inv ≫ D.map signActionGenerator) ≫ atBase.hom ≅ inversion)
    (inversionSquared :
      HyperbolicOrbicurve.Hom.TwoIso
        (HyperbolicOrbicurve.Hom.comp inversion inversion)
        (HyperbolicOrbicurve.Hom.id X)) :
    OrbicurveSignAction X where
  diagram := D
  atBase := atBase
  inversion := inversion
  generator_identification := generator_identification
  inversionSquared := inversionSquared

#check signActionDiagramOf
#check orbicurveSignActionOf
#print axioms orbicurveSignActionOf

end
end Iut
