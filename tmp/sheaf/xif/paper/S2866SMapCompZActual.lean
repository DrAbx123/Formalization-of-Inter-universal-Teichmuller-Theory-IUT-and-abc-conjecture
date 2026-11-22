import tmp.sheaf.xif.paper.S2865SMapFinActual
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2866SMapCompZActual
open Iut
open LeanFormal.IUT.XiFPaper.S2858Z2MapCompActual
open LeanFormal.IUT.XiFPaper.S2865SMapFinActual
variable {F : Type u} [Field F]
variable (X : Iut.HyperbolicOrbicurve F)
variable (inv : X.Hom X)
variable (invSq : Iut.HyperbolicOrbicurve.Hom.TwoIso
  (Iut.HyperbolicOrbicurve.Hom.comp inv inv) (Iut.HyperbolicOrbicurve.Hom.id X))

theorem eq_one_of_toFin_zero {g : SignGroup} (h : signGroupToFin g = 0) : g = 1 := by
  rcases signGroup_cases g with hg | hg
  · exact hg
  · rw [hg] at h
    simp [signGroupToFin] at h

theorem eq_gen_of_toFin_one {g : SignGroup} (h : signGroupToFin g = 1) :
    g = Multiplicative.ofAdd (1 : ZMod 2) := by
  rcases signGroup_cases g with hg | hg
  · rw [hg] at h
    simp [signGroupToFin] at h
  · exact hg

noncomputable def leftUnitorIso (f : X.stack.fiber ⟶ X.stack.fiber) :
    @Iso (X.stack.fiber ⟶ X.stack.fiber)
      (Pseudofunctor.StrongTrans.homCategory (F := X.stack.fiber) (G := X.stack.fiber))
      (𝟙 X.stack.fiber ≫ f) f :=
  Iso.mk (Bicategory.leftUnitor f).hom (Bicategory.leftUnitor f).inv (by simp) (by simp)

noncomputable def rightUnitorIso (f : X.stack.fiber ⟶ X.stack.fiber) :
    @Iso (X.stack.fiber ⟶ X.stack.fiber)
      (Pseudofunctor.StrongTrans.homCategory (F := X.stack.fiber) (G := X.stack.fiber))
      (f ≫ 𝟙 X.stack.fiber) f :=
  Iso.mk (Bicategory.rightUnitor f).hom (Bicategory.rightUnitor f).inv (by simp) (by simp)

noncomputable def sqIso :
    @Iso (X.stack.fiber ⟶ X.stack.fiber)
      (Pseudofunctor.StrongTrans.homCategory (F := X.stack.fiber) (G := X.stack.fiber))
      (𝟙 X.stack.fiber) (inv ≫ inv) :=
  @Iso.mk (X.stack.fiber ⟶ X.stack.fiber)
    (Pseudofunctor.StrongTrans.homCategory (F := X.stack.fiber) (G := X.stack.fiber))
    (𝟙 X.stack.fiber) (inv ≫ inv) invSq.inv invSq.hom (by simp) (by simp)

noncomputable def sMapCompZ (f g : SignGroup) :
    sMapZ X inv (g * f) ≅ sMapZ X inv f ≫ sMapZ X inv g :=
  match hf : signGroupToFin f, hg : signGroupToFin g with
  | 0, 0 => by
      rw [eq_one_of_toFin_zero hf, eq_one_of_toFin_zero hg]
      simpa [sMapZ_one, mul_one, one_mul, invM] using
        (leftUnitorIso X (𝟙 X.stack.fiber)).symm
  | 0, 1 => by
      rw [eq_one_of_toFin_zero hf, eq_gen_of_toFin_one hg]
      simpa [sMapZ_one, sMapZ_gen, invM, mul_one, one_mul, invM] using
        (leftUnitorIso X (invM X inv)).symm
  | 1, 0 => by
      rw [eq_gen_of_toFin_one hf, eq_one_of_toFin_zero hg]
      simpa [sMapZ_one, sMapZ_gen, invM, mul_one, one_mul, invM] using
        (rightUnitorIso X (invM X inv)).symm
  | 1, 1 => by
      rw [eq_gen_of_toFin_one hf, eq_gen_of_toFin_one hg]
      have h : Multiplicative.ofAdd (1 : ZMod 2) *
          Multiplicative.ofAdd (1 : ZMod 2) = 1 := by decide
      rw [h]
      simpa [sMapZ_one, sMapZ_gen, invM, mul_one, one_mul, invM] using sqIso X inv invSq



@[simp] theorem sMapCompZ_one_one :
    sMapCompZ X inv invSq 1 1 =
      (leftUnitorIso X (𝟙 X.stack.fiber)).symm := rfl

@[simp] theorem sMapCompZ_one_gen :
    sMapCompZ X inv invSq 1 (Multiplicative.ofAdd (1 : ZMod 2)) =
      (leftUnitorIso X (invM X inv)).symm := rfl

@[simp] theorem sMapCompZ_gen_one :
    sMapCompZ X inv invSq (Multiplicative.ofAdd (1 : ZMod 2)) 1 =
      (rightUnitorIso X (invM X inv)).symm := rfl

@[simp] theorem sMapCompZ_gen_gen :
    sMapCompZ X inv invSq
      (Multiplicative.ofAdd (1 : ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 2)) =
      sqIso X inv invSq := rfl

#check sMapCompZ
#print axioms sMapCompZ

end LeanFormal.IUT.XiFPaper.S2866SMapCompZActual