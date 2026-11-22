import tmp.sheaf.xif.paper.S3076MapCompV3
import tmp.sheaf.xif.paper.S3076QPrimeNatIsoActual
import tmp.sheaf.xif.paper.S3074PullbackFunctor
import tmp.sheaf.xif.paper.S3075QPrimeAssembly
import tmp.sheaf.xif.paper.S3076MapIdObjHelper
import tmp.sheaf.xif.paper.S3073PullbackTotalBridge
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3074PullbackFunctor
open LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S3076MapCompV3
open LeanFormal.IUT.XiFPaper.S3076MapIdObjHelper
namespace LeanFormal.IUT.XiFPaper.S3076MapCompUnitFstProbeAdapted
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

variable {U V : LocallyDiscrete (Iut.SchemeOverField S2994A6Stackification.S2994A6K)ᵒᵖ}
variable (f : U ⟶ V)
variable (P : S3048SignTorsorFiber U)

abbrev idMor (U : LocallyDiscrete (Iut.SchemeOverField S2994A6Stackification.S2994A6K)ᵒᵖ) : U ⟶ U := 𝟙 U

noncomputable def toB'' :
    S3073PullbackTotal (U := U) (V := V) (f := f) P ⟶
      ((S3075PullbackFunctor f).obj
        ((S3075PullbackFunctor (𝟙 U)).obj P)).total :=
  (show (S3073PullbackFiber (U := U) (V := V) (f := f)
      (S3073PullbackFiber (U := U) (V := U) (f := 𝟙 U) P)).total =
      ((S3075PullbackFunctor f).obj ((S3075PullbackFunctor (𝟙 U)).obj P)).total from rfl) ▸
    toB' (U := U) (V := U) (W := V) (f := 𝟙 U) (g := f) P

theorem S3076MapCompUnitLeft_fst :
    (toB'' f P ≫
      ((S3075PullbackFunctor f).map
        ((LeanFormal.IUT.XiFPaper.S3076QPrimeNatIsoActual.S3076MapId U).hom.app P)).hom) ≫
      pullback.fst (f := P.projection) (g := f.as.unop) =
    𝟙 (S3073PullbackTotal (U := U) (V := V) (f := f) P) ≫
      pullback.fst (f := P.projection) (g := f.as.unop) := by
  rw [show toB'' f P =
      pullback.lift
        (toC' (U := U) (V := U) (W := V) (f := 𝟙 U) (g := f) P)
        (pullback.snd (f := P.projection) (g := ((𝟙 U ≫ f).as.unop))) _ from rfl]
  rw [Category.assoc]
  rw [show ((S3075PullbackFunctor f).map
      ((LeanFormal.IUT.XiFPaper.S3076QPrimeNatIsoActual.S3076MapId U).hom.app P)).hom =
      S3074Map f ((LeanFormal.IUT.XiFPaper.S3076QPrimeNatIsoActual.S3076MapId U).hom.app P) from rfl]
  rw [S3074Map, pullback.lift_fst]
  rw [← Category.assoc]
  simp only [S3073PullbackTotal_eq_obj_total,
    obj_total_eq_S3073PullbackTotal]
  rw [pullback.lift_fst]
  simp only [S3076MapIdObj_hom, idMor_as_unop, pullback.lift_fst,
    Category.comp_id, Category.id_comp]

#check S3076MapCompUnitLeft_fst
#check toB''
end LeanFormal.IUT.XiFPaper.S3076MapCompUnitFstProbeAdapted
end
