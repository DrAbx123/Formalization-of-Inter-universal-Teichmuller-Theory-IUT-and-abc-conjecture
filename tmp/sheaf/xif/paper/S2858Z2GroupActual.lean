import tmp.sheaf.xif.paper.S2858Z2MapCompActual
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2858Z2GroupActual
open Iut
open LeanFormal.IUT.XiFPaper.S2858Z2MapCompActual
variable {F : Type u} [Field F]
variable (X : Iut.HyperbolicOrbicurve F)
variable (inv : X.Hom X)
variable (invSq : Iut.HyperbolicOrbicurve.Hom.TwoIso
  (Iut.HyperbolicOrbicurve.Hom.comp inv inv) (Iut.HyperbolicOrbicurve.Hom.id X))

noncomputable def sMapCompGroup (f g : SignGroup) :
    sMap X inv (g * f) ≅ sMap X inv f ≫ sMap X inv g := by
  by_cases hf : f = 1
  · subst f
    by_cases hg : g = 1
    · subst g
      simpa [sMap] using
        (λ_ (𝟙 X.stack.fiber : X.stack.fiber ⟶ X.stack.fiber)).symm
    · have hg' : g = Multiplicative.ofAdd 1 := by
        rcases signGroup_cases g with h | h
        · exact absurd h hg
        · exact h
      subst g
      simpa [sMap] using
        (λ_ (show X.stack.fiber ⟶ X.stack.fiber from inv)).symm
  · have hf' : f = Multiplicative.ofAdd 1 := by
      rcases signGroup_cases f with h | h
      · exact absurd h hf
      · exact h
    by_cases hg : g = 1
    · subst f; subst g
      simpa [sMap] using
        (ρ_ (show X.stack.fiber ⟶ X.stack.fiber from inv)).symm
    · have hg' : g = Multiplicative.ofAdd 1 := by
        rcases signGroup_cases g with h | h
        · exact absurd h hg
        · exact h
      subst f; subst g
      have h : Multiplicative.ofAdd (1 : ZMod 2) *
          Multiplicative.ofAdd 1 = 1 := by decide
      rw [h]
      simp [sMap]
      change (𝟙 X.stack.fiber : X.stack.fiber ⟶ X.stack.fiber) ≅
        HyperbolicOrbicurve.Hom.comp inv inv
      exact invSq.symm


noncomputable def sMapCompC {b₀ b₁ b₂ : SingleObj SignGroup}
    (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    sMap X inv (f ≫ g) ≅ sMap X inv f ≫ sMap X inv g :=
  sMapCompGroup X inv invSq (show SignGroup from f) (show SignGroup from g)

noncomputable def sMapIdC (b : SingleObj SignGroup) :
    sMap X inv (𝟙 b) ≅ (𝟙 X.stack.fiber : X.stack.fiber ⟶ X.stack.fiber) := by
  rw [CategoryTheory.SingleObj.id_as_one]
  simp [sMap]
  exact Iso.refl _

#check sMapCompGroup
#check sMapCompC
#check sMapIdC
#print axioms sMapCompGroup
#print axioms sMapCompC
#print axioms sMapIdC

end LeanFormal.IUT.XiFPaper.S2858Z2GroupActual