import tmp.sheaf.xif.paper.S2858Z2MapCompActual
import tmp.sheaf.xif.paper.S2867CastEqHelperActual
import Mathlib.Tactic.CategoryTheory.Bicategory.PureCoherence
set_option maxHeartbeats 8000000
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2859CoherentFinalActual
open Iut
open LeanFormal.IUT.XiFPaper.S2858Z2MapCompActual
open LeanFormal.IUT.XiFPaper.S2867CastEqHelperActual
variable {F : Type u} [Field F]
variable (X : Iut.HyperbolicOrbicurve F)
variable (inv : X.Hom X)
variable (invSq : Iut.HyperbolicOrbicurve.Hom.TwoIso
  (Iut.HyperbolicOrbicurve.Hom.comp inv inv) (Iut.HyperbolicOrbicurve.Hom.id X))

theorem eq_gen_of_ne_one (g : SignGroup) (hg : g ≠ 1) :
    g = Multiplicative.ofAdd (1 : ZMod 2) := by
  rcases signGroup_cases g with h | h
  · exact absurd h hg
  · exact h

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

@[simp] theorem leftUnitorIso_eq (f : X.stack.fiber ⟶ X.stack.fiber) :
    leftUnitorIso X f = Bicategory.leftUnitor f := Iso.ext rfl

@[simp] theorem rightUnitorIso_eq (f : X.stack.fiber ⟶ X.stack.fiber) :
    rightUnitorIso X f = Bicategory.rightUnitor f := Iso.ext rfl

@[simp] theorem sqIso_eq : sqIso X inv invSq = invSq.symm := Iso.ext rfl

theorem cast_iso_inv {C : Type*} [Category C] {X Y : C}
    (h : (X ≅ Y) = (X ≅ Y)) (i : X ≅ Y) :
    (cast h i).inv = i.inv := by
  cases h; rfl

theorem cast_iso_hom {C : Type*} [Category C] {X Y : C}
    (h : (X ≅ Y) = (X ≅ Y)) (i : X ≅ Y) :
    (cast h i).hom = i.hom := by
  cases h; rfl

theorem gen_mul_gen :
    Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide

noncomputable def sMapCompGroup (X : Iut.HyperbolicOrbicurve F) (inv : X.Hom X)
    (invSq : Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp inv inv) (Iut.HyperbolicOrbicurve.Hom.id X))
    (f g : SignGroup) :
    sMap X inv (g * f) ≅ sMap X inv f ≫ sMap X inv g :=
  if hf : f = 1 then
    if hg : g = 1 then
      (by simpa [sMap, hf, hg] using (leftUnitorIso X (𝟙 X.stack.fiber)).symm)
    else
      (by simpa [sMap, hf, hg] using
        (leftUnitorIso X (show X.stack.fiber ⟶ X.stack.fiber from inv)).symm)
  else
    if hg : g = 1 then
      (by simpa [sMap, hf, hg] using
        (rightUnitorIso X (show X.stack.fiber ⟶ X.stack.fiber from inv)).symm)
    else
      (by rw [eq_gen_of_ne_one f hf, eq_gen_of_ne_one g hg, gen_mul_gen]; simpa [sMap] using sqIso X inv invSq)

noncomputable def sMapIdC (b : SingleObj SignGroup) :
    sMap X inv (𝟙 b) ≅ (𝟙 X.stack.fiber : X.stack.fiber ⟶ X.stack.fiber) := by
  rw [CategoryTheory.SingleObj.id_as_one]
  simp [sMap]
  exact Iso.refl _

noncomputable def sMapCompC {b₀ b₁ b₂ : SingleObj SignGroup}
    (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    sMap X inv (f ≫ g) ≅ sMap X inv f ≫ sMap X inv g :=
  sMapCompGroup X inv invSq (show SignGroup from f) (show SignGroup from g)

@[simp] theorem sMapCompGroup_one_one :
    sMapCompGroup X inv invSq 1 1 =
      (leftUnitorIso X (𝟙 X.stack.fiber)).symm := by
  simp [sMapCompGroup]
  exact eq_of_heq (cast_heq _ _)

@[simp] theorem sMapCompGroup_one_gen :
    sMapCompGroup X inv invSq 1 (Multiplicative.ofAdd (1 : ZMod 2)) =
      (leftUnitorIso X (show X.stack.fiber ⟶ X.stack.fiber from inv)).symm := by
  simp [sMapCompGroup]
  exact eq_of_heq (cast_heq _ _)

@[simp] theorem sMapCompGroup_gen_one :
    sMapCompGroup X inv invSq (Multiplicative.ofAdd (1 : ZMod 2)) 1 =
      (rightUnitorIso X (show X.stack.fiber ⟶ X.stack.fiber from inv)).symm := by
  simp [sMapCompGroup]
  exact eq_of_heq (cast_heq _ _)

@[simp] theorem sMapCompGroup_gen_gen :
    sMapCompGroup X inv invSq
      (Multiplicative.ofAdd (1 : ZMod 2))
      (Multiplicative.ofAdd (1 : ZMod 2)) =
      (sqIso X inv invSq) := by
  simp [sMapCompGroup]
  exact eq_of_heq (cast_heq _ _)

noncomputable def diagramC : SignActionIndex ⥤ᵖ EtaleStackPseudofunctor F :=
  Iut.signActionDiagramOf (F := F)
    (fun _ => X.stack.fiber)
    (fun {b b'} (f : b ⟶ b') => sMap X inv f)
    (fun b => sMapIdC X inv b)
    (fun {b₀ b₁ b₂} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) => sMapCompC X inv invSq f g)
    (by
      intro b₀ b₁ b₂ b₃ f g h
      rcases signGroup_cases f with rfl | rfl <;>
      rcases signGroup_cases g with rfl | rfl <;>
      rcases signGroup_cases h with rfl | rfl <;>
      have hgg : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
      dsimp [sMapCompC]
      simp only [sMap, sMap_one, sMap_gen, sMapCompC, sMapCompGroup, sMapIdC,
        sMapCompGroup_one_one, sMapCompGroup_one_gen,
        sMapCompGroup_gen_one, sMapCompGroup_gen_gen,
        SingleObj.comp_as_mul, SingleObj.id_as_one, gen_mul_gen,
        Category.id_comp, Category.comp_id,
        leftUnitorIso_eq, rightUnitorIso_eq, sqIso_eq, hgg]
      repeat (split_ifs <;> simp_all)
      all_goals try rw [eqToHom_trans, eqToHom_refl]
      all_goals try rfl
      all_goals try exact eq_of_heq (cast_heq _ _)
      all_goals try (rw [Iso.inv_hom_id]; simp)
      all_goals try bicategory_coherence)
    (by
      intro b₀ b₁ f
      rcases signGroup_cases f with rfl | rfl <;>
      simp [sMap, sMapCompC, sMapCompGroup, sMapIdC,
        SingleObj.comp_as_mul, SingleObj.id_as_one,
        leftUnitorIso_eq, rightUnitorIso_eq, sqIso_eq])
    (by
      intro b₀ b₁ f
      rcases signGroup_cases f with rfl | rfl <;>
      simp [sMap, sMapCompC, sMapCompGroup, sMapIdC,
        SingleObj.comp_as_mul, SingleObj.id_as_one,
        leftUnitorIso_eq, rightUnitorIso_eq, sqIso_eq])

#check diagramC
#print axioms diagramC

end LeanFormal.IUT.XiFPaper.S2859CoherentFinalActual