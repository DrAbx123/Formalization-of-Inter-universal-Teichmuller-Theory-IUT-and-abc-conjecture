import tmp.sheaf.xif.paper.S3128OfHMapActual
import tmp.sheaf.xif.paper.S3128PrestackActual
import tmp.sheaf.xif.paper.S3128QuotientSheafStrongActual
open CategoryTheory CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S3128SheafTorsorActual
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafObjActual
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafStrongActual
open LeanFormal.IUT.XiFPaper.S3128OfHMapActual
open LeanFormal.IUT.XiFPaper.S3128PrestackActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.S3128OfHObjectActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable {U : SchemeOverField F} (H : Over U ⥤ Over U)
variable (hH : ∀ V : (Over U)ᵒᵖ, H.op.obj V ≅ V)

noncomputable def S3128BaseChangeOfH' (A : S3128ZMod2QuotientSheafObj (F:=F) (X:=X) U) :
    S3128ZMod2QuotientSheafObj (F:=F) (X:=X) U where
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
  mapPoint := fun V p =>
    (S3128OfHHMap H hH V).obj (A.mapPoint (H.op.obj V) p)

noncomputable def S3128OfHHom {A B : S3128ZMod2QuotientSheafObj (F:=F) (X:=X) U}
    (φ : S3128StrongHom A B) :
    S3128StrongHom (S3128BaseChangeOfH' H hH A)
      (S3128BaseChangeOfH' H hH B) where
  pointsIso := S3128WhiskerLeftIso H.op φ.pointsIso
  equivariant := by
    intro g
    apply NatTrans.ext
    funext V
    simp [S3128WhiskerLeftIso, S3128BaseChangeOfH',
      Functor.whiskerLeft_app]
    exact congrArg (fun e => e.app (H.op.obj V)) (φ.equivariant g)
  mapCompat := fun V p =>
    (S3128OfHHMap H hH V).mapIso (φ.mapCompat (H.op.obj V) p)

#check S3128OfHHom
#check S3128BaseChangeOfH'
end LeanFormal.IUT.XiFPaper.S3128OfHObjectActual