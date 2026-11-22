import tmp.sheaf.xif.paper.S3128QuotientSheafStrongActual
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S3128SheafTorsorActual
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafObjActual
open LeanFormal.IUT.XiFPaper.S3128FiberTypeActual
namespace LeanFormal.IUT.XiFPaper.S3128BaseChangeOfHActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable {U : SchemeOverField F}

noncomputable def S3128BaseChangeOfH
    (H : Over U ⥤ Over U)
    (hH : ∀ V, (H.op.obj V).unop.left = V.unop.left)
    (A : S3128ZMod2QuotientSheafObj (F := F) (X := X) U) :
    S3128ZMod2QuotientSheafObj (F := F) (X := X) U where
  points := H.op ⋙ A.points
  action := by
    exact
      { toFun := fun g =>
          { app := fun V => (A.action g).app (H.op.obj V)
            naturality := by
              intro V W φ
              exact (A.action g).naturality (H.op.map φ) }
        map_one' := by
          apply NatTrans.ext
          funext V
          exact congrArg (fun e => e.app (H.op.obj V)) (map_one A.action)
        map_mul' := by
          intro g h
          apply NatTrans.ext
          funext V
          exact congrArg (fun e => e.app (H.op.obj V)) (map_mul A.action g h) }
  torsor := by
    intro V p q
    exact A.torsor (H.op.obj V) p q
  mapPoint := by
    intro V p
    exact cast (congrArg
      (fun s => S3128FiberType (LocallyDiscrete.mk (Opposite.op s)))
      (hH V)) (A.mapPoint (H.op.obj V) p)

#check S3128BaseChangeOfH

def S3128OfHTest (f : U ⟶ U) (A : S3128ZMod2QuotientSheafObj (F := F) (X := X) U) :
    S3128ZMod2QuotientSheafObj (F := F) (X := X) U :=
  S3128BaseChangeOfH (Over.map f) (fun V => rfl) A
end LeanFormal.IUT.XiFPaper.S3128BaseChangeOfHActual