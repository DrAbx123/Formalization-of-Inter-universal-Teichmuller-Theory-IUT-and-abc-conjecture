import tmp.sheaf.xif.paper.S3076QPrimeMapCompActual
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
open LeanFormal.IUT.XiFPaper.S3076QPrimeMapCompActual
namespace LeanFormal.IUT.XiFPaper.S3076ToCActionProbe2
set_option maxHeartbeats 4000000

abbrev C : Type 1 := Iut.SchemeOverField S2994A6K
variable {U V W : LocallyDiscrete Cᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable (P : S3048SignTorsorFiber U) (γ : Iut.SignGroup)

abbrev E {U : LocallyDiscrete Cᵒᵖ} (P : S3048SignTorsorFiber U) :
    P.total ⟶ U.as.unop :=
  P.projection
abbrev F {U V : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V) :
    V.as.unop ⟶ U.as.unop :=
  f.as.unop
abbrev G {V W : LocallyDiscrete Cᵒᵖ} (g : V ⟶ W) :
    W.as.unop ⟶ V.as.unop :=
  g.as.unop
abbrev A {U V W : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (P : S3048SignTorsorFiber U) : Iut.SchemeOverField S2994A6K :=
  pullback (E P) (G g ≫ F f)
abbrev Cc {U V : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V)
    (P : S3048SignTorsorFiber U) : Iut.SchemeOverField S2994A6K :=
  pullback (E P) (F f)

noncomputable def toC {U V W : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (P : S3048SignTorsorFiber U) : A f g P ⟶ Cc f P :=
  pullback.lift
    (pullback.fst (f := E P) (g := G g ≫ F f))
    (pullback.snd (f := E P) (g := G g ≫ F f) ≫ G g)
    (by
      calc
        pullback.fst (f := E P) (g := G g ≫ F f) ≫ E P
            = pullback.snd (f := E P) (g := G g ≫ F f) ≫ (G g ≫ F f) :=
              pullback.condition
        _ = (pullback.snd (f := E P) (g := G g ≫ F f) ≫ G g) ≫ F f := by
              rw [Category.assoc])

noncomputable def actionA {U V W : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (P : S3048SignTorsorFiber U) (γ : Iut.SignGroup) : A f g P ⟶ A f g P :=
  pullback.lift
    (pullback.fst (f := E P) (g := G g ≫ F f) ≫ P.action γ)
    (pullback.snd (f := E P) (g := G g ≫ F f))
    (by
      calc
        (pullback.fst (f := E P) (g := G g ≫ F f) ≫ P.action γ) ≫ E P
            = pullback.fst (f := E P) (g := G g ≫ F f) ≫ (P.action γ ≫ P.projection) := by
              rw [Category.assoc]
        _ = pullback.fst (f := E P) (g := G g ≫ F f) ≫ E P := by
              rw [P.action_projection]
        _ = pullback.snd (f := E P) (g := G g ≫ F f) ≫ (G g ≫ F f) :=
              pullback.condition)

noncomputable def actionC {U V : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V)
    (P : S3048SignTorsorFiber U) (γ : Iut.SignGroup) : Cc f P ⟶ Cc f P :=
  pullback.lift
    (pullback.fst (f := E P) (g := F f) ≫ P.action γ)
    (pullback.snd (f := E P) (g := F f))
    (by
      calc
        (pullback.fst (f := E P) (g := F f) ≫ P.action γ) ≫ E P
            = pullback.fst (f := E P) (g := F f) ≫ (P.action γ ≫ P.projection) := by
              rw [Category.assoc]
        _ = pullback.fst (f := E P) (g := F f) ≫ E P := by
              rw [P.action_projection]
        _ = pullback.snd (f := E P) (g := F f) ≫ F f :=
              pullback.condition)

theorem toC_action {U V W : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (P : S3048SignTorsorFiber U) (γ : Iut.SignGroup) :
    toC f g P ≫ actionC f P γ = actionA f g P γ ≫ toC f g P := by
  apply pullback.hom_ext (f := E P) (g := F f)
  · rw [Category.assoc]
    simp only [actionC, pullback.lift_fst]
    rw [← Category.assoc]
    unfold toC
    rw [pullback.lift_fst]
    rw [Category.assoc]
    rw [pullback.lift_fst]
    unfold actionA
    rw [pullback.lift_fst]
  · rw [Category.assoc]
    simp only [actionC, pullback.lift_snd]
    unfold toC
    rw [pullback.lift_snd]
    rw [Category.assoc]
    rw [pullback.lift_snd]
    unfold actionA
    rw [← Category.assoc, pullback.lift_snd]

#check toC_action

end LeanFormal.IUT.XiFPaper.S3076ToCActionProbe2
