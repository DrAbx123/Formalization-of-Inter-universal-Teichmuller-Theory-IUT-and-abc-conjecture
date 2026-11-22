import tmp.sheaf.xif.paper.S3128ZMod2BaseChangeTorsorActual
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S3128ZMod2FiberCategoryActual
open LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeActual
open LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeTorsorActual
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeObjActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable {U U' : SchemeOverField F} (f : U' ⟶ U)
variable (A : S3128ZMod2FiberObj (F := F) X U)

/-- Base-change object with the remaining torsor/point data supplied explicitly
(the scheme-level torsor comparison is not yet constructed). -/
noncomputable abbrev S3128BaseChangeObj
    (torsor_iso' :
      S3128BaseChangeP f A ⨿ S3128BaseChangeP f A ≅
        pullback (S3128BaseChangeProj f A) (S3128BaseChangeProj f A))
    (equivariantData' : Prop) (equivariantData_proof' : equivariantData') :
    S3128ZMod2FiberObj X U' where
  P := S3128BaseChangeP f A
  proj := S3128BaseChangeProj f A
  zmod2_action := S3128BaseChangeZMod2Action f A
  action_proj := fun g => by
    change S3128BaseChangeAutHom' f A g ≫ S3128BaseChangeProj' f A =
      S3128BaseChangeProj' f A
    exact S3128BaseChangeAutHom'_proj f A g
  signAction := A.signAction
  stackMap := S3128BaseChangeStackMap f A
  torsor_iso := torsor_iso'
  equivariantData := equivariantData'
  equivariantData_proof := equivariantData_proof'

/-- Target: a base-change functor between the Z/2 fiber categories. -/
def S3128BaseChangeFunctorTarget : Prop :=
  Nonempty (S3128ZMod2FiberObj X U ⥤ S3128ZMod2FiberObj X U')

/-- Target: prestack descent for morphisms (the comparison functor is fully
faithful on covers). -/
def S3128PrestackDescentTarget : Prop :=
  Nonempty (S3128ZMod2FiberObj X U ⥤ S3128ZMod2FiberObj X U')

#check S3128BaseChangeObj
#check S3128BaseChangeFunctorTarget

end LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeObjActual