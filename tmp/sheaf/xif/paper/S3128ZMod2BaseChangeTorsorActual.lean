import tmp.sheaf.xif.paper.S3128ZMod2ConstantGroupActual
import tmp.sheaf.xif.paper.S3128ZMod2BaseChangeActual
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S3128ZMod2FiberCategoryActual
open LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeActual
open LeanFormal.IUT.XiFPaper.S3128ZMod2ConstantGroupActual
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeTorsorActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable {U U' : SchemeOverField F} (f : U' ⟶ U)
variable (A : S3128ZMod2FiberObj (F := F) X U)

abbrev S3128BaseChangeP' : SchemeOverField F :=
  S3128BaseChangeP f A

abbrev S3128BaseChangeProj' : S3128BaseChangeP' f A ⟶ U' :=
  S3128BaseChangeProj f A

abbrev S3128BaseChangeAutHom' (g : Multiplicative (ZMod 2)) :
    S3128BaseChangeP' f A ⟶ S3128BaseChangeP' f A :=
  ((S3128BaseChangeZMod2Aut f A g :
    S3128BaseChangeP' f A ≅ S3128BaseChangeP' f A)).hom

theorem S3128BaseChangeAutHom'_proj (g : Multiplicative (ZMod 2)) :
    S3128BaseChangeAutHom' f A g ≫ S3128BaseChangeProj' f A =
      S3128BaseChangeProj' f A := by
  simp only [S3128BaseChangeAutHom', S3128BaseChangeZMod2Aut,
    S3128BaseChangeZMod2Hom, S3128BaseChangeProj', pullback.lift_snd]

noncomputable def S3128BaseChangeTorsorMapZero :
    S3128BaseChangeP' f A ⟶
      pullback (S3128BaseChangeProj' f A) (S3128BaseChangeProj' f A) :=
  pullback.lift (𝟙 _) (𝟙 _) (by simp)

noncomputable def S3128BaseChangeTorsorMapOne :
    S3128BaseChangeP' f A ⟶
      pullback (S3128BaseChangeProj' f A) (S3128BaseChangeProj' f A) :=
  pullback.lift
    (S3128BaseChangeAutHom' f A S3128ZMod2Generator)
    (𝟙 _)
    (by
      rw [Category.id_comp]
      exact S3128BaseChangeAutHom'_proj f A S3128ZMod2Generator)

noncomputable def S3128TorsorMapBaseChange :
    S3128BaseChangeP' f A ⨿ S3128BaseChangeP' f A ⟶
      pullback (S3128BaseChangeProj' f A) (S3128BaseChangeProj' f A) :=
  coprod.desc
    (S3128BaseChangeTorsorMapZero f A)
    (S3128BaseChangeTorsorMapOne f A)

def S3128TorsorIsoBaseChangeTarget : Prop :=
  IsIso (S3128TorsorMapBaseChange f A)

#check S3128TorsorMapBaseChange
#check S3128TorsorIsoBaseChangeTarget

end LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeTorsorActual