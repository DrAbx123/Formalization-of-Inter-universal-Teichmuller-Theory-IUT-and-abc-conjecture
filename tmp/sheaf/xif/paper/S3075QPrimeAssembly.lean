import tmp.sheaf.xif.paper.S3074PullbackFunctor
import tmp.sheaf.xif.paper.S3072QPrimePseudofunctor

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3074PullbackFunctor
open LeanFormal.IUT.XiFPaper.S3072QPrimePseudofunctor
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly

@[simp] theorem S3049TorsorIso_comp_hom
    {U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
    {P Q R : S3048SignTorsorFiber U}
    (f : S3049TorsorIso U P Q) (g : S3049TorsorIso U Q R) :
    ((S3069CategoryStruct U).comp f g).hom = f.hom ≫ g.hom := rfl

@[simp] theorem S3049TorsorIso_id_hom
    {U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
    (P : S3048SignTorsorFiber U) :
    ((S3069CategoryStruct U).id P).hom = 𝟙 P.total := rfl

noncomputable def S3075PullbackFunctor
    {U V : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
    (f : U ⟶ V) :
    S3048SignTorsorFiber U ⥤ S3048SignTorsorFiber V where
  obj P := S3073PullbackFiber f P
  map h := S3074MapIso f h
  map_id P := by
    apply S3049TorsorIso.ext
    dsimp [S3074MapIso, S3074Map, S3069CategoryStruct]
    apply pullback.hom_ext (f := P.projection) (g := f.as.unop)
    · rw [pullback.lift_fst]
      change pullback.fst P.projection f.as.unop ≫ 𝟙 P.total =
        𝟙 (S3073PullbackFiber f P).total ≫ pullback.fst P.projection f.as.unop
      simp
    · rw [pullback.lift_snd]
      change pullback.snd P.projection f.as.unop =
        𝟙 (S3073PullbackFiber f P).total ≫ pullback.snd P.projection f.as.unop
      simp
  map_comp h k := by
    apply S3049TorsorIso.ext
    dsimp [S3074MapIso, S3074Map]
    apply pullback.hom_ext (g := f.as.unop)
    · conv_rhs =>
        rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
          pullback.lift_fst]
      rw [pullback.lift_fst, Category.assoc]
    · simp [pullback.lift_snd]

#check S3075PullbackFunctor

end LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly
end
