import tmp.sheaf.xif.paper.S2869Z2CoherentDataActual
import tmp.sheaf.xif.paper.S2866SMapCompZActual
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2870Z2CoherentDataActual
open Iut
open LeanFormal.IUT.XiFPaper.S2858Z2MapCompActual
open LeanFormal.IUT.XiFPaper.S2865SMapFinActual
open LeanFormal.IUT.XiFPaper.S2866SMapCompZActual
open LeanFormal.IUT.XiFPaper.S2869Z2CoherentDataActual
variable {F : Type u} [Field F]
variable (X : Iut.HyperbolicOrbicurve F)
variable (inv : X.Hom X)
variable (invSq : Iut.HyperbolicOrbicurve.Hom.TwoIso
  (Iut.HyperbolicOrbicurve.Hom.comp inv inv) (Iut.HyperbolicOrbicurve.Hom.id X))
set_option maxHeartbeats 8000000

noncomputable def coherentData : Z2CoherentData (F := F) X where
  map := fun {a b} (f : a ⟶ b) => sMapZ X inv (show SignGroup from f)
  mapId := fun a => by
    have h : sMapZ X inv (show SignGroup from (𝟙 a)) = 𝟙 X.stack.fiber := by
      simp [SingleObj.id_as_one, sMapZ_one]
    rw [h]
  mapComp := fun {a b c} (f : a ⟶ b) (g : b ⟶ c) =>
    sMapCompZ X inv invSq (show SignGroup from f) (show SignGroup from g)
  map₂_associator := by
    intro a b c d f g h
    rcases signGroup_cases f with rfl | rfl <;>
    rcases signGroup_cases g with rfl | rfl <;>
    rcases signGroup_cases h with rfl | rfl <;>
    rw [show signGroupToFin ((1 : SignGroup) * 1) = signGroupToFin 1 from by rw [mul_one]] at *
    dsimp [sMapCompZ]
    simp only [one_mul, mul_one, sMapFin, sMapFin_zero, sMapFin_one,
      signGroupToFin_one, signGroupToFin_gen,
      SingleObj.comp_as_mul, SingleObj.id_as_one, sMapCompZ,
      leftUnitorIso, rightUnitorIso, sqIso]
    all_goals (repeat (split_ifs <;> split <;> simp_all))
    all_goals try rw [invSq.inv_hom_id]
    all_goals try bicategory_coherence
  map₂_left_unitor := by
    intro a b f
    rcases signGroup_cases f with rfl | rfl <;>
    dsimp [sMapCompZ]
    simp only [one_mul, mul_one, sMapFin, sMapFin_zero, sMapFin_one,
      signGroupToFin_one, signGroupToFin_gen,
      SingleObj.comp_as_mul, SingleObj.id_as_one, sMapCompZ,
      leftUnitorIso, rightUnitorIso, sqIso]
    all_goals (repeat (split_ifs <;> split <;> simp_all))
    all_goals try bicategory_coherence
  map₂_right_unitor := by
    intro a b f
    rcases signGroup_cases f with rfl | rfl <;>
    dsimp [sMapCompZ]
    simp only [sMapZ, sMapZ_one, sMapZ_gen, SingleObj.comp_as_mul, SingleObj.id_as_one,
      sMapCompZ, leftUnitorIso, rightUnitorIso, sqIso]
    repeat (split_ifs <;> simp_all)
    all_goals try bicategory_coherence

#check coherentData

end LeanFormal.IUT.XiFPaper.S2870Z2CoherentDataActual
end
