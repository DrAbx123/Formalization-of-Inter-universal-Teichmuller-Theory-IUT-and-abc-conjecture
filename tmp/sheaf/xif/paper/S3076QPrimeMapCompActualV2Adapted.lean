import tmp.sheaf.xif.paper.S3073TorsorPullbackActual
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
namespace LeanFormal.IUT.XiFPaper.S3076QPrimeMapCompActualV2Adapted
set_option maxHeartbeats 4000000

abbrev C : Type 1 := Iut.SchemeOverField S2994A6K
variable {U V W : LocallyDiscrete Cᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable (P : S3048SignTorsorFiber U)

abbrev E : P.total ⟶ U.as.unop := P.projection
abbrev F : V.as.unop ⟶ U.as.unop := f.as.unop
abbrev G : W.as.unop ⟶ V.as.unop := g.as.unop

abbrev A : Iut.SchemeOverField S2994A6K :=
  (S3073PullbackFiber (U := U) (V := W) (f := f ≫ g) P).total
abbrev B : Iut.SchemeOverField S2994A6K :=
  (S3073PullbackFiber (U := V) (V := W) (f := g)
    (S3073PullbackFiber (U := U) (V := V) (f := f) P)).total
abbrev Cc : Iut.SchemeOverField S2994A6K :=
  (S3073PullbackFiber (U := U) (V := V) (f := f) P).total

noncomputable def toA : B f g P ⟶ A f g P := by
  change pullback (pullback.snd (E P) (F f)) (G g) ⟶
    pullback (E P) ((f ≫ g).as.unop)
  exact pullback.lift
    (pullback.fst (f := pullback.snd (E P) (F f)) (g := G g) ≫
      pullback.fst (f := E P) (g := (f ≫ g).as.unop))
    (pullback.snd (f := pullback.snd (E P) (F f)) (g := G g))
    (by
      calc
        (pullback.fst (f := pullback.snd (E P) (F f)) (g := G g) ≫
            pullback.fst (f := E P) (g := (f ≫ g).as.unop)) ≫ E P
            = pullback.fst (f := pullback.snd (E P) (F f)) (g := G g) ≫
                (pullback.fst (f := E P) (g := (f ≫ g).as.unop) ≫ E P) := by
              rw [Category.assoc]
        _ = pullback.fst (f := pullback.snd (E P) (F f)) (g := G g) ≫
              (pullback.snd (f := E P) (g := (f ≫ g).as.unop) ≫
                (f ≫ g).as.unop) := by
              rw [pullback.condition]
        _ = (pullback.fst (f := pullback.snd (E P) (F f)) (g := G g) ≫
              pullback.snd (f := E P) (g := (f ≫ g).as.unop)) ≫
              (f ≫ g).as.unop := by rw [Category.assoc]
        _ = (pullback.snd (f := pullback.snd (E P) (F f)) (g := G g) ≫ G g) ≫
              (f ≫ g).as.unop := by
                rw [pullback.condition (f := pullback.snd (E P) (F f)) (g := G g)]
        _ = pullback.snd (f := pullback.snd (E P) (F f)) (g := G g) ≫
              ((f ≫ g).as.unop) := by rw [Category.assoc])

noncomputable def toB : A f g P ⟶ B f g P := by
  change pullback (E P) ((f ≫ g).as.unop) ⟶
    pullback (pullback.snd (E P) (F f)) (G g)
  exact pullback.lift
    (pullback.lift
      (pullback.fst (f := E P) (g := (f ≫ g).as.unop))
      (pullback.snd (f := E P) (g := (f ≫ g).as.unop) ≫ G g)
      (by
        calc
          pullback.fst (f := E P) (g := (f ≫ g).as.unop) ≫ E P
              = pullback.snd (f := E P) (g := (f ≫ g).as.unop) ≫
                  ((f ≫ g).as.unop) := pullback.condition
          _ = (pullback.snd (f := E P) (g := (f ≫ g).as.unop) ≫ G g) ≫
                  F f := by
                rw [show (f ≫ g).as.unop = G g ≫ F f from rfl, Category.assoc]))
    (pullback.snd (f := E P) (g := (f ≫ g).as.unop))
    (by rw [pullback.lift_snd])

noncomputable def toC : A f g P ⟶ Cc f P := by
  change pullback (E P) ((f ≫ g).as.unop) ⟶ pullback (E P) (F f)
  exact pullback.lift
    (pullback.fst (f := E P) (g := (f ≫ g).as.unop))
    (pullback.snd (f := E P) (g := (f ≫ g).as.unop) ≫ G g)
    (by
      rw [Category.assoc]
      exact pullback.condition)

#check toA
#check toB
#check toC

end LeanFormal.IUT.XiFPaper.S3076QPrimeMapCompActualV2Adapted