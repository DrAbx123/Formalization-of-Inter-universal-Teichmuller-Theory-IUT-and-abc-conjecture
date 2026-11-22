import tmp.sheaf.xif.paper.S2858Z2MapCompActual
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2858Z2GroupFinActual
open Iut
open LeanFormal.IUT.XiFPaper.S2858Z2MapCompActual
variable {F : Type u} [Field F]
variable (X : Iut.HyperbolicOrbicurve F)
variable (inv : X.Hom X)
variable (invSq : Iut.HyperbolicOrbicurve.Hom.TwoIso
  (Iut.HyperbolicOrbicurve.Hom.comp inv inv) (Iut.HyperbolicOrbicurve.Hom.id X))

noncomputable def e (g : SignGroup) : Fin 2 :=
  if g = 1 then 0 else 1

theorem one_ne_gen : (1 : SignGroup) ≠ Multiplicative.ofAdd (1 : ZMod 2) := by decide

theorem gen_ne_one : Multiplicative.ofAdd (1 : ZMod 2) ≠ (1 : SignGroup) := by decide

theorem eq_gen_of_ne_one (g : SignGroup) (hg : g ≠ 1) :
    g = Multiplicative.ofAdd (1 : ZMod 2) := by
  rcases signGroup_cases g with h | h
  · exact absurd h hg
  · exact h

theorem eq_one_of_e_zero {g : SignGroup} (h : e g = 0) : g = 1 := by
  by_contra hg
  have hgen : g = Multiplicative.ofAdd (1 : ZMod 2) := eq_gen_of_ne_one g hg
  rw [hgen] at h
  simp [e, gen_ne_one] at h

theorem eq_gen_of_e_one {g : SignGroup} (h : e g = 1) :
    g = Multiplicative.ofAdd (1 : ZMod 2) := by
  by_contra hg
  have h1 : g = 1 := by
    rcases signGroup_cases g with h' | h'
    · exact h'
    · exact absurd h' hg
  rw [h1] at h
  simp [e] at h

noncomputable def sMapCompGroup (f g : SignGroup) :
    sMap X inv (g * f) ≅ sMap X inv f ≫ sMap X inv g :=
  match hf : e f, hg : e g with
  | 0, 0 => by
      rw [eq_one_of_e_zero hf, eq_one_of_e_zero hg]
      simpa [sMap] using
        (λ_ (𝟙 X.stack.fiber : X.stack.fiber ⟶ X.stack.fiber)).symm
  | 0, 1 => by
      rw [eq_one_of_e_zero hf, eq_gen_of_e_one hg]
      simpa [sMap] using
        (λ_ (show X.stack.fiber ⟶ X.stack.fiber from inv)).symm
  | 1, 0 => by
      rw [eq_gen_of_e_one hf, eq_one_of_e_zero hg]
      simpa [sMap] using
        (ρ_ (show X.stack.fiber ⟶ X.stack.fiber from inv)).symm
  | 1, 1 => by
      rw [eq_gen_of_e_one hf, eq_gen_of_e_one hg]
      have h : Multiplicative.ofAdd (1 : ZMod 2) *
          Multiplicative.ofAdd (1 : ZMod 2) = 1 := by decide
      rw [h]
      simp [sMap]
      change (𝟙 X.stack.fiber : X.stack.fiber ⟶ X.stack.fiber) ≅
        HyperbolicOrbicurve.Hom.comp inv inv
      exact invSq.symm


@[simp] theorem sMapCompGroup_one_one :
    sMapCompGroup X inv invSq 1 1 =
      (λ_ (𝟙 X.stack.fiber : X.stack.fiber ⟶ X.stack.fiber)).symm := by
  simp [sMapCompGroup, e, gen_ne_one]
  exact cast_eq _ _

@[simp] theorem sMapCompGroup_one_gen :
    sMapCompGroup X inv invSq 1 (Multiplicative.ofAdd (1 : ZMod 2)) =
      (λ_ (show X.stack.fiber ⟶ X.stack.fiber from inv)).symm := by
  simp [sMapCompGroup, e, gen_ne_one]
  exact cast_eq _ _

@[simp] theorem sMapCompGroup_gen_one :
    sMapCompGroup X inv invSq (Multiplicative.ofAdd (1 : ZMod 2)) 1 =
      (ρ_ (show X.stack.fiber ⟶ X.stack.fiber from inv)).symm := by
  simp [sMapCompGroup, e, gen_ne_one]
  exact cast_eq _ _

@[simp] theorem sMapCompGroup_gen_gen :
    sMapCompGroup X inv invSq
      (Multiplicative.ofAdd (1 : ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 2)) =
      invSq.symm := by
  simp [sMapCompGroup, e, gen_ne_one]
  exact cast_eq _ _

#check sMapCompGroup
#print axioms sMapCompGroup

end LeanFormal.IUT.XiFPaper.S2858Z2GroupFinActual