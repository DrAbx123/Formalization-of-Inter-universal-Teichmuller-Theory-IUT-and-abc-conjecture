import tmp.sheaf.xif.paper.S3075QPrimeAssembly
import tmp.sheaf.xif.paper.S3074PullbackFunctor
import tmp.sheaf.xif.paper.S3076QPrimeNatIsoActual
import tmp.sheaf.xif.paper.S3073PullbackTotalBridge
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly
open LeanFormal.IUT.XiFPaper.S3074PullbackFunctor
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
namespace LeanFormal.IUT.XiFPaper.S3076MapCompUnitObjProbe
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

abbrev C : Type 1 := Iut.SchemeOverField S2994A6Stackification.S2994A6K
variable {U V W : LocallyDiscrete Cᵒᵖ}

abbrev Aobj {U V : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V)
    (P : S3048SignTorsorFiber U) : Iut.SchemeOverField S2994A6Stackification.S2994A6K :=
  pullback P.projection f.as.unop

@[simp] lemma Aobj_total_bridge {U V : LocallyDiscrete Cᵒᵖ}
    (f : U ⟶ V) (P : S3048SignTorsorFiber U) :
    Aobj f P = ((S3075PullbackFunctor f).obj P).total := rfl

noncomputable abbrev toC'_obj {U V W : LocallyDiscrete Cᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (P : S3048SignTorsorFiber U) :
    Aobj (f ≫ g) P ⟶ Aobj f P :=
  pullback.lift
    (pullback.fst (f := P.projection) (g := (f ≫ g).as.unop))
    (pullback.snd (f := P.projection) (g := (f ≫ g).as.unop) ≫ g.as.unop)
    (by
      calc
        pullback.fst (f := P.projection) (g := (f ≫ g).as.unop) ≫ P.projection
            = pullback.snd (f := P.projection) (g := (f ≫ g).as.unop) ≫
                (f ≫ g).as.unop := pullback.condition
        _ = (pullback.snd (f := P.projection) (g := (f ≫ g).as.unop) ≫
                g.as.unop) ≫ f.as.unop := by
              rw [show (f ≫ g).as.unop = g.as.unop ≫ f.as.unop from rfl,
                Category.assoc])

noncomputable abbrev toB'_obj {U V W : LocallyDiscrete Cᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (P : S3048SignTorsorFiber U) :
    Aobj (f ≫ g) P ⟶ Aobj g (S3073PullbackFiber f P) :=
  pullback.lift
    (toC'_obj f g P)
    (pullback.snd (f := P.projection) (g := (f ≫ g).as.unop))
    (by
      show toC'_obj f g P ≫ S3073PullbackProjection f P =
        pullback.snd (f := P.projection) (g := (f ≫ g).as.unop) ≫ g.as.unop
      rw [toC'_obj, pullback.lift_snd])

noncomputable abbrev mapIdRaw {U : LocallyDiscrete Cᵒᵖ}
    (P : S3048SignTorsorFiber U) :
    S3049TorsorIso U
      (S3073PullbackFiber (U := U) (V := U) (f := 𝟙 U) P) P :=
  (LeanFormal.IUT.XiFPaper.S3076QPrimeNatIsoActual.S3076MapId U).hom.app P

theorem S3076MapCompUnitLeft_fst
    (f : U ⟶ V) (P : S3048SignTorsorFiber U) :
    (toB'_obj (U := U) (V := U) (W := V) (f := 𝟙 U) (g := f) P ≫
      S3074Map f (mapIdRaw (U := U) P)) ≫
      pullback.fst (f := P.projection) (g := f.as.unop) =
    𝟙 (Aobj f P) ≫ pullback.fst (f := P.projection) (g := f.as.unop) := by
  rw [show toB'_obj (U := U) (V := U) (W := V) (f := 𝟙 U) (g := f) P =
      pullback.lift
        (toC'_obj (U := U) (V := U) (W := V) (f := 𝟙 U) (g := f) P)
        (pullback.snd (f := P.projection) (g := ((𝟙 U ≫ f).as.unop))) _ from rfl]
  rw [Category.assoc]
  rw [S3074Map, pullback.lift_fst]
  rw [← Category.assoc]
  rw [pullback.lift_fst]
  simp only [pullback.lift_fst, Category.comp_id, Category.id_comp]
  rw [toC'_obj, pullback.lift_fst]
  unfold mapIdRaw
  simp [LeanFormal.IUT.XiFPaper.S3076QPrimeNatIsoActual.S3076MapId,
    LeanFormal.IUT.XiFPaper.S3076QPrimeNatIsoActual.S3076MapIdIsoObj,
    pullback.lift_fst, Category.comp_id, Category.id_comp]

#check toC'_obj
#check toB'_obj
#check S3076MapCompUnitLeft_fst
end LeanFormal.IUT.XiFPaper.S3076MapCompUnitObjProbe
end
