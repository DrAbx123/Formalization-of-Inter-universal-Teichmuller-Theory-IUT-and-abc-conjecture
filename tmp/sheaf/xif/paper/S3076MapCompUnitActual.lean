import tmp.sheaf.xif.paper.S3076MapCompV3
import tmp.sheaf.xif.paper.S3076QPrimeNatIsoActual
import tmp.sheaf.xif.paper.S3074PullbackFunctor
import tmp.sheaf.xif.paper.S3075QPrimeAssembly
import tmp.sheaf.xif.paper.S3069QPrimeTorsorStack
import tmp.sheaf.xif.paper.S3076MapIdObjHelper
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
namespace LeanFormal.IUT.XiFPaper.S3076MapCompUnitActual
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

variable {U V : LocallyDiscrete (Iut.SchemeOverField S2994A6Stackification.S2994A6K)ᵒᵖ}
variable (f : U ⟶ V)
variable (P : S3048SignTorsorFiber U)

theorem S3076MapCompUnitLeft :
    toB' (U := U) (V := U) (W := V) (f := 𝟙 U) (g := f) P ≫
      ((S3075PullbackFunctor f).map
        ((LeanFormal.IUT.XiFPaper.S3076QPrimeNatIsoActual.S3076MapId U).hom.app P)).hom =
      𝟙 (S3073PullbackTotal (U := U) (V := V) (f := f) P) := by
  apply pullback.hom_ext (f := P.projection) (g := f.as.unop)
  · change (toB' (U := U) (V := U) (W := V) (f := 𝟙 U) (g := f) P).hom ≫
        ((S3075PullbackFunctor f).map
          ((LeanFormal.IUT.XiFPaper.S3076QPrimeNatIsoActual.S3076MapId U).hom.app P)).hom =
      (𝟙 (S3073PullbackTotal (U := U) (V := V) (f := f) P)).hom
    rw [show toB' (U := U) (V := U) (W := V) (f := 𝟙 U) (g := f) P =
        pullback.lift
          (toC' (U := U) (V := U) (W := V) (f := 𝟙 U) (g := f) P)
          (pullback.snd (f := P.projection)
            (g := ((𝟙 U ≫ f).as.unop))) _ from rfl,
      pullback.lift_fst]
    simp only [LeanFormal.IUT.XiFPaper.S3076MapIdObjHelper.S3076MapIdObj_hom,
      LeanFormal.IUT.XiFPaper.S3076MapIdObjHelper.idMor_as_unop,
      pullback.lift_fst, Category.comp_id, Category.id_comp]
  · rw [show toB' (U := U) (V := U) (W := V) (f := 𝟙 U) (g := f) P =
        pullback.lift
          (toC' (U := U) (V := U) (W := V) (f := 𝟙 U) (g := f) P)
          (pullback.snd (f := P.projection)
            (g := ((𝟙 U ≫ f).as.unop))) _ from rfl,
      pullback.lift_snd]
    simp only [Category.comp_id, Category.id_comp]

#check S3076MapCompUnitLeft
end LeanFormal.IUT.XiFPaper.S3076MapCompUnitActual
end
