import tmp.sheaf.xif.paper.S2858Z2MapCompActual
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2858Z2GroupIfActualAdapted
open Iut
open LeanFormal.IUT.XiFPaper.S2858Z2MapCompActual
variable {F : Type u} [Field F]
variable (X : Iut.HyperbolicOrbicurve F)
variable (inv : X.Hom X)
variable (invSq : Iut.HyperbolicOrbicurve.Hom.TwoIso
  (Iut.HyperbolicOrbicurve.Hom.comp inv inv) (Iut.HyperbolicOrbicurve.Hom.id X))

theorem one_ne_gen : (1 : SignGroup) ≠ Multiplicative.ofAdd (1 : ZMod 2) := by decide
theorem gen_ne_one : Multiplicative.ofAdd (1 : ZMod 2) ≠ (1 : SignGroup) := by decide

theorem eq_gen_of_ne_one (g : SignGroup) (hg : g ≠ 1) :
    g = Multiplicative.ofAdd (1 : ZMod 2) := by
  rcases signGroup_cases g with h | h
  · exact absurd h hg
  · exact h


noncomputable def leftUnitorIso (f : X.stack.fiber ⟶ X.stack.fiber) :
    @Iso (X.stack.fiber ⟶ X.stack.fiber)
      (Pseudofunctor.StrongTrans.homCategory (F := X.stack.fiber) (G := X.stack.fiber))
      (𝟙 X.stack.fiber ≫ f) f :=
  Iso.mk (Bicategory.leftUnitor f).hom (Bicategory.leftUnitor f).inv
    (by simp) (by simp)

noncomputable def rightUnitorIso (f : X.stack.fiber ⟶ X.stack.fiber) :
    @Iso (X.stack.fiber ⟶ X.stack.fiber)
      (Pseudofunctor.StrongTrans.homCategory (F := X.stack.fiber) (G := X.stack.fiber))
      (f ≫ 𝟙 X.stack.fiber) f :=
  Iso.mk (Bicategory.rightUnitor f).hom (Bicategory.rightUnitor f).inv
    (by simp) (by simp)

noncomputable def sqIso :
    @Iso (X.stack.fiber ⟶ X.stack.fiber)
      (Pseudofunctor.StrongTrans.homCategory (F := X.stack.fiber) (G := X.stack.fiber))
      (𝟙 X.stack.fiber) (inv ≫ inv) :=
  @Iso.mk (X.stack.fiber ⟶ X.stack.fiber)
    (Pseudofunctor.StrongTrans.homCategory (F := X.stack.fiber) (G := X.stack.fiber))
    (𝟙 X.stack.fiber) (inv ≫ inv) invSq.inv invSq.hom (by simp) (by simp)


noncomputable def sMapCompGroup (f g : SignGroup) :
    sMap X inv (g * f) ≅ sMap X inv f ≫ sMap X inv g :=
  if hf : f = 1 then
    if hg : g = 1 then
      (by
        subst f; subst g
        simpa [sMap] using
          (leftUnitorIso X (𝟙 X.stack.fiber)).symm)
    else
      (by
        subst f
        rw [eq_gen_of_ne_one g hg]
        simpa [sMap] using
          (leftUnitorIso X (show X.stack.fiber ⟶ X.stack.fiber from inv)).symm)
  else
    if hg : g = 1 then
      (by
        subst g
        rw [eq_gen_of_ne_one f hf]
        simpa [sMap] using
          (rightUnitorIso X (show X.stack.fiber ⟶ X.stack.fiber from inv)).symm)
    else
      (by
        rw [eq_gen_of_ne_one f hf, eq_gen_of_ne_one g hg]
        have h : Multiplicative.ofAdd (1 : ZMod 2) *
            Multiplicative.ofAdd (1 : ZMod 2) = 1 := by decide
        rw [h]
        simp [sMap]
        change (𝟙 X.stack.fiber : X.stack.fiber ⟶ X.stack.fiber) ≅
          HyperbolicOrbicurve.Hom.comp inv inv
        exact sqIso X inv invSq)

@[simp] theorem sMapCompGroup_one_one :
    sMapCompGroup X inv invSq 1 1 =
      (leftUnitorIso X (𝟙 X.stack.fiber)).symm := by
  simp only [sMapCompGroup]
  split_ifs <;> simp_all
  all_goals simp_all [one_ne_gen, gen_ne_one]


@[simp] theorem sMapCompGroup_one_gen :
    sMapCompGroup X inv invSq 1 (Multiplicative.ofAdd (1 : ZMod 2)) =
      (leftUnitorIso X (show X.stack.fiber ⟶ X.stack.fiber from inv)).symm := by
  simp only [sMapCompGroup]
  split_ifs <;> simp_all
  all_goals simp_all [one_ne_gen, gen_ne_one]

@[simp] theorem sMapCompGroup_gen_one :
    sMapCompGroup X inv invSq (Multiplicative.ofAdd (1 : ZMod 2)) 1 =
      (rightUnitorIso X (show X.stack.fiber ⟶ X.stack.fiber from inv)).symm := by
  simp only [sMapCompGroup]
  split_ifs <;> simp_all
  all_goals simp_all [one_ne_gen, gen_ne_one]

@[simp] theorem sMapCompGroup_gen_gen :
    sMapCompGroup X inv invSq
      (Multiplicative.ofAdd (1 : ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 2)) =
      sqIso X inv invSq := by
  simp only [sMapCompGroup]
  split_ifs <;> simp_all
  all_goals simp_all [one_ne_gen, gen_ne_one]

#check sMapCompGroup
#check sMapCompGroup_one_one
#print axioms sMapCompGroup
#print axioms sMapCompGroup_one_one

end LeanFormal.IUT.XiFPaper.S2858Z2GroupIfActualAdapted