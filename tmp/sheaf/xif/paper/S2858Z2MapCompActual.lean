import tmp.sheaf.xif.paper.S2852OrbicurveSignActionCoherentActual
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2858Z2MapCompActual
open Iut
variable {F : Type u} [Field F]
variable (X : Iut.HyperbolicOrbicurve F)
variable (inv : X.Hom X)
variable (invSq : Iut.HyperbolicOrbicurve.Hom.TwoIso
  (Iut.HyperbolicOrbicurve.Hom.comp inv inv) (Iut.HyperbolicOrbicurve.Hom.id X))

theorem signGroup_cases (g : SignGroup) :
    g = 1 ∨ g = Multiplicative.ofAdd (1 : ZMod 2) := by
  obtain ⟨a, ha⟩ : ∃ a : ZMod 2, g = Multiplicative.ofAdd a :=
    ⟨g.toAdd, (ofAdd_toAdd g).symm⟩
  rw [ha]
  fin_cases a
  · left; rfl
  · right; rfl

def sMap (g : SignGroup) : X.stack.fiber ⟶ X.stack.fiber :=
  if g = 1 then 𝟙 X.stack.fiber else inv

theorem sMap_one : sMap X inv 1 = 𝟙 X.stack.fiber := by
  simp [sMap]

theorem sMap_gen :
    sMap X inv (Multiplicative.ofAdd (1 : ZMod 2)) = inv := by
  simp [sMap]

noncomputable def sMapComp {b₀ b₁ b₂ : SingleObj SignGroup}
    (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    sMap X inv (f ≫ g) ≅ sMap X inv f ≫ sMap X inv g :=
  Classical.choice (by
    let f' : SignGroup := f
    let g' : SignGroup := g
    change Nonempty (sMap X inv (g' * f') ≅
      sMap X inv f' ≫ sMap X inv g')
    rcases signGroup_cases f' with hf | hf <;>
      rcases signGroup_cases g' with hg | hg
    · rw [hf, hg]
      exact ⟨(λ_ (𝟙 X.stack.fiber)).symm⟩
    · rw [hf, hg]
      exact ⟨(λ_ (show X.stack.fiber ⟶ X.stack.fiber from inv)).symm⟩
    · rw [hf, hg]
      exact ⟨(ρ_ (show X.stack.fiber ⟶ X.stack.fiber from inv)).symm⟩
    · have h : Multiplicative.ofAdd (1 : ZMod 2) *
          Multiplicative.ofAdd (1 : ZMod 2) = 1 := by decide
      rw [hf, hg, h]
      exact ⟨by
        change (𝟙 X.stack.fiber) ≅
          HyperbolicOrbicurve.Hom.comp inv inv
        exact invSq.symm⟩)


#check signGroup_cases
#check sMap
#check sMapComp
#print axioms signGroup_cases
#print axioms sMapComp

end LeanFormal.IUT.XiFPaper.S2858Z2MapCompActual
