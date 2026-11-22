import tmp.sheaf.xif.paper.S2852OrbicurveSignActionCoherentActual
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2869Z2CoherentDataActual
open Iut
variable {F : Type u} [Field F]

/-- Exact remaining data for a coherent Z/2-action diagram on a constant object. -/
structure Z2CoherentData (X : Iut.HyperbolicOrbicurve F) where
  map : ∀ {a b : SingleObj SignGroup},
    (a ⟶ b) → (X.stack.fiber ⟶ X.stack.fiber)
  mapId : ∀ a : SingleObj SignGroup,
    map (𝟙 a) ≅ 𝟙 (X.stack.fiber)
  mapComp : ∀ {a b c : SingleObj SignGroup}
    (f : a ⟶ b) (g : b ⟶ c),
    map (f ≫ g) ≅ map f ≫ map g
  map₂_associator : ∀ {a b c d : SingleObj SignGroup}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
    (mapComp (f ≫ g) h).hom ≫
      (mapComp f g).hom ▷ map h ≫
      (α_ (map f) (map g) (map h)).hom ≫
      map f ◁ (mapComp g h).inv ≫
      (mapComp f (g ≫ h)).inv = eqToHom (by simp)
  map₂_left_unitor : ∀ {a b : SingleObj SignGroup} (f : a ⟶ b),
    (mapComp (𝟙 a) f).hom ≫
      (mapId a).hom ▷ map f ≫
      (λ_ (map f)).hom = eqToHom (by simp)
  map₂_right_unitor : ∀ {a b : SingleObj SignGroup} (f : a ⟶ b),
    (mapComp f (𝟙 b)).hom ≫
      map f ◁ (mapId b).hom ≫
      (ρ_ (map f)).hom = eqToHom (by simp)

#check Z2CoherentData
end LeanFormal.IUT.XiFPaper.S2869Z2CoherentDataActual
