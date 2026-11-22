import tmp.sheaf.xif.paper.S3076QPrimeMapCompActual
import tmp.sheaf.xif.paper.S3075QPrimeAssembly
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3076QPrimeMapCompActual
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open Iut
namespace LeanFormal.IUT.XiFPaper.S3076CompUnitProbe
set_option maxHeartbeats 4000000

variable {U V W : LocallyDiscrete Cᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable (P : S3048SignTorsorFiber U)

noncomputable def S3076CompToC : S3076CompA f g P ⟶ S3076CompC f P :=
  pullback.lift
    (pullback.fst (f := S3076CompE P) (g := (S3076CompG g) ≫ (S3076CompF f)))
    (pullback.snd (f := S3076CompE P) (g := (S3076CompG g) ≫ (S3076CompF f)) ≫
      S3076CompG g)
    (by
      rw [Category.assoc]
      exact pullback.condition (f := S3076CompE P)
        (g := (S3076CompG g) ≫ (S3076CompF f)))

noncomputable def S3076CompToB : S3076CompA f g P ⟶ S3076CompB f g P :=
  pullback.lift
    (S3076CompToC f g P)
    (pullback.snd (f := S3076CompE P) (g := (S3076CompG g) ≫ (S3076CompF f)))
    (by
      show S3076CompToC f g P ≫
          pullback.snd (f := S3076CompE P) (g := S3076CompF f) =
        pullback.snd (f := S3076CompE P) (g := (S3076CompG g) ≫ (S3076CompF f)) ≫
          S3076CompG g
      rw [S3076CompToC, pullback.lift_snd])

theorem S3076ToA_toC :
    S3076CompToA f g P ≫ S3076CompToC f g P =
      pullback.fst (f := pullback.snd (f := S3076CompE P) (g := S3076CompF f))
        (g := S3076CompG g) := by
  apply pullback.hom_ext (f := S3076CompE P) (g := S3076CompF f)
  · rw [Category.assoc]
    unfold S3076CompToC
    rw [pullback.lift_fst]
    unfold S3076CompToA
    rw [pullback.lift_fst]
  · rw [Category.assoc]
    unfold S3076CompToC
    rw [pullback.lift_snd]
    unfold S3076CompToA
    rw [← Category.assoc]
    rw [pullback.lift_snd]
    rw [pullback.condition (f := pullback.snd (f := S3076CompE P) (g := S3076CompF f))
      (g := S3076CompG g)]

theorem S3076CompToA_toB :
    S3076CompToA f g P ≫ S3076CompToB f g P = 𝟙 (S3076CompB f g P) := by
  apply pullback.hom_ext
    (f := pullback.snd (f := S3076CompE P) (g := S3076CompF f))
    (g := S3076CompG g)
  · rw [Category.assoc]
    unfold S3076CompToB
    rw [pullback.lift_fst]
    rw [S3076ToA_toC]
    simp
  · rw [Category.assoc]
    unfold S3076CompToB
    rw [pullback.lift_snd]
    unfold S3076CompToA
    rw [pullback.lift_snd]
    simp


theorem S3076CompToB_toA :
    S3076CompToB f g P ≫ S3076CompToA f g P = 𝟙 (S3076CompA f g P) := by
  apply pullback.hom_ext (f := S3076CompE P)
    (g := (S3076CompG g) ≫ (S3076CompF f))
  · rw [Category.assoc]
    unfold S3076CompToA
    rw [pullback.lift_fst]
    rw [← Category.assoc]
    unfold S3076CompToB
    rw [pullback.lift_fst]
    unfold S3076CompToC
    rw [pullback.lift_fst]
    simp
  · rw [Category.assoc]
    unfold S3076CompToA
    rw [pullback.lift_snd]
    unfold S3076CompToB
    rw [pullback.lift_snd]
    simp


noncomputable def S3076CompIsoObj :
    S3076CompA f g P ≅ S3076CompB f g P :=
  Iso.mk
    (S3076CompToB f g P)
    (S3076CompToA f g P)
    (S3076CompToB_toA f g P)
    (S3076CompToA_toB f g P)






theorem S3076ToC_action (h : SignGroup) :
    S3076CompToC f g P ≫ (S3073PullbackFiber f P).action h =
      (S3073PullbackFiber (f ≫ g) P).action h ≫ S3076CompToC f g P := by
  apply pullback.hom_ext (f := S3076CompE P) (g := S3076CompF f)
  · rw [Category.assoc, Category.assoc]
    simp only [S3076CompToC, S3073PullbackAction]
    rw [pullback.lift_fst]
    rw [Category.assoc]
    rw [pullback.lift_fst]
    rw [Category.assoc]
  · rw [Category.assoc, Category.assoc]
    simp only [S3076CompToC, S3073PullbackAction]
    rw [pullback.lift_snd]
    rw [Category.assoc]
    rw [pullback.lift_snd]
    rw [Category.assoc]

#check S3076ToC_action

#check S3076CompIsoObj
end LeanFormal.IUT.XiFPaper.S3076CompUnitProbe
end
