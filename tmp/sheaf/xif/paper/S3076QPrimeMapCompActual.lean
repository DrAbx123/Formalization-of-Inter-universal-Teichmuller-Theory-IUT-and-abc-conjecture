import tmp.sheaf.xif.paper.S3076QPrimeNatIsoActual
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
namespace LeanFormal.IUT.XiFPaper.S3076QPrimeMapCompActual
set_option maxHeartbeats 4000000

abbrev C : Type 1 := Iut.SchemeOverField S2994A6K

variable {U V W : LocallyDiscrete Cᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable (P : S3048SignTorsorFiber U)

abbrev S3076CompE : P.total ⟶ U.as.unop := P.projection
abbrev S3076CompF : V.as.unop ⟶ U.as.unop := f.as.unop
abbrev S3076CompG : W.as.unop ⟶ V.as.unop := g.as.unop

abbrev S3076CompA : Iut.SchemeOverField S2994A6K :=
  pullback (S3076CompE P) ((S3076CompG g) ≫ (S3076CompF f))
abbrev S3076CompC : Iut.SchemeOverField S2994A6K :=
  pullback (S3076CompE P) (S3076CompF f)
abbrev S3076CompB : Iut.SchemeOverField S2994A6K :=
  pullback (pullback.snd (S3076CompE P) (S3076CompF f)) (S3076CompG g)

noncomputable def S3076CompToA : S3076CompB f g P ⟶ S3076CompA f g P :=
  pullback.lift
    (pullback.fst (f := pullback.snd (S3076CompE P) (S3076CompF f)) (g := (S3076CompG g)) ≫
      pullback.fst (f := (S3076CompE P)) (g := (S3076CompF f)))
    (pullback.snd (f := pullback.snd (S3076CompE P) (S3076CompF f)) (g := (S3076CompG g)))
    (by
      calc
        (pullback.fst (f := pullback.snd (S3076CompE P) (S3076CompF f))
              (g := (S3076CompG g)) ≫
            pullback.fst (f := (S3076CompE P)) (g := (S3076CompF f))) ≫
            (S3076CompE P)
            = pullback.fst (f := pullback.snd (S3076CompE P) (S3076CompF f))
                (g := (S3076CompG g)) ≫
                (pullback.fst (f := (S3076CompE P)) (g := (S3076CompF f)) ≫
                  (S3076CompE P)) := by rw [Category.assoc]
        _ = pullback.fst (f := pullback.snd (S3076CompE P) (S3076CompF f))
              (g := (S3076CompG g)) ≫
              (pullback.snd (f := (S3076CompE P)) (g := (S3076CompF f)) ≫
                (S3076CompF f)) := by
                rw [pullback.condition (f := (S3076CompE P)) (g := (S3076CompF f))]
        _ = (pullback.fst (f := pullback.snd (S3076CompE P) (S3076CompF f))
              (g := (S3076CompG g)) ≫
              pullback.snd (f := (S3076CompE P)) (g := (S3076CompF f))) ≫
              (S3076CompF f) := by rw [Category.assoc]
        _ = (pullback.snd (f := pullback.snd (S3076CompE P) (S3076CompF f))
              (g := (S3076CompG g)) ≫ (S3076CompG g)) ≫ (S3076CompF f) := by
                rw [pullback.condition (f := pullback.snd (S3076CompE P) (S3076CompF f))
                  (g := (S3076CompG g))]
        _ = pullback.snd (f := pullback.snd (S3076CompE P) (S3076CompF f))
              (g := (S3076CompG g)) ≫ ((S3076CompG g) ≫ (S3076CompF f)) := by
                rw [Category.assoc])

#check S3076CompA
#check S3076CompB
#check S3076CompToA


noncomputable def S3076CompToB : S3076CompA f g P ⟶ S3076CompB f g P :=
  pullback.lift
    (pullback.lift
      (pullback.fst (f := S3076CompE P) (g := S3076CompG g ≫ S3076CompF f))
      (pullback.snd (f := S3076CompE P) (g := S3076CompG g ≫ S3076CompF f) ≫ S3076CompG g)
      (by
        calc
          pullback.fst (f := S3076CompE P) (g := S3076CompG g ≫ S3076CompF f) ≫
              S3076CompE P
              = pullback.snd (f := S3076CompE P)
                  (g := S3076CompG g ≫ S3076CompF f) ≫
                  (S3076CompG g ≫ S3076CompF f) :=
                pullback.condition
          _ = (pullback.snd (f := S3076CompE P)
                (g := S3076CompG g ≫ S3076CompF f) ≫ S3076CompG g) ≫
                S3076CompF f := by rw [Category.assoc]))
    (pullback.snd (f := S3076CompE P) (g := S3076CompG g ≫ S3076CompF f))
    (by
      rw [pullback.lift_snd])

#check S3076CompToB



#check S3076CompToA
#check S3076CompToB



#check S3076CompToA
#check S3076CompToB



#check S3076CompToA
#check S3076CompToB



#check S3076CompToA
#check S3076CompToB


noncomputable def S3076CompToC : S3076CompA f g P ⟶ S3076CompC f P :=
  pullback.lift
    (pullback.fst (f := S3076CompE P) (g := S3076CompG g ≫ S3076CompF f))
    (pullback.snd (f := S3076CompE P) (g := S3076CompG g ≫ S3076CompF f) ≫ S3076CompG g)
    (by
      rw [Category.assoc]
      exact pullback.condition)

theorem S3076ToA_toC :
    S3076CompToA f g P ≫ S3076CompToC f g P =
      pullback.fst (f := pullback.snd (S3076CompE P) (S3076CompF f))
        (g := S3076CompG g) := by
  apply pullback.hom_ext
    (f := S3076CompE P) (g := S3076CompF f)
  · conv_lhs => rw [Category.assoc]
    rw [S3076CompToC]
    rw [pullback.lift_fst]
    rw [S3076CompToA]
    rw [pullback.lift_fst]
  · rw [S3076CompToA, S3076CompToC]
    rw [Category.assoc]
    rw [pullback.lift_snd]
    conv_lhs => rw [← Category.assoc]
    rw [pullback.lift_snd]
    rw [pullback.condition]

#check S3076CompToC
#check S3076ToA_toC


theorem S3076CompToA_toB :
    S3076CompToA f g P ≫ S3076CompToB f g P =
      𝟙 (S3076CompB f g P) := by
  apply pullback.hom_ext
    (f := pullback.snd (S3076CompE P) (S3076CompF f))
    (g := S3076CompG g)
  · rw [Category.id_comp]
    rw [Category.assoc]
    rw [S3076CompToB]
    rw [pullback.lift_fst]
    change S3076CompToA f g P ≫ S3076CompToC f g P = _
    rw [S3076ToA_toC]
  · rw [Category.id_comp]
    rw [Category.assoc]
    rw [S3076CompToB]
    rw [pullback.lift_snd]
    rw [S3076CompToA]
    rw [pullback.lift_snd]

#check S3076CompToA_toB
#print axioms S3076CompToA_toB


theorem S3076CompToB_toA :
    S3076CompToB f g P ≫ S3076CompToA f g P =
      𝟙 (S3076CompA f g P) := by
  apply pullback.hom_ext
    (f := S3076CompE P) (g := S3076CompG g ≫ S3076CompF f)
  · rw [Category.id_comp]
    rw [Category.assoc]
    rw [S3076CompToA]
    rw [pullback.lift_fst]
    rw [← Category.assoc]
    rw [S3076CompToB]
    rw [pullback.lift_fst]
    rw [pullback.lift_fst]
  · rw [Category.id_comp]
    rw [Category.assoc]
    rw [S3076CompToA]
    rw [pullback.lift_snd]
    rw [S3076CompToB]
    rw [pullback.lift_snd]

#check S3076CompToB_toA
#print axioms S3076CompToB_toA

noncomputable def S3076CompTotalIso :
    S3076CompA f g P ≅ S3076CompB f g P :=
  Iso.mk (S3076CompToB f g P) (S3076CompToA f g P)
    (S3076CompToB_toA f g P) (S3076CompToA_toB f g P)

#check S3076CompTotalIso
#print axioms S3076CompTotalIso



#check S3076CompToA_toB
#check S3076CompToB_toA
#check S3076CompTotalIso



#check S3076CompToA_toB
#check S3076CompToB_toA
#check S3076CompTotalIso

end LeanFormal.IUT.XiFPaper.S3076QPrimeMapCompActual