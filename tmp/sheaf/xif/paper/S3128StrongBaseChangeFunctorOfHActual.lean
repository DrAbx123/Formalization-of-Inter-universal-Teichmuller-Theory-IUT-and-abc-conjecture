import tmp.sheaf.xif.paper.S3128OfHObjectActual
import tmp.sheaf.xif.paper.S3128OfHHomLemmasActual
import tmp.sheaf.xif.paper.S3128OfHHelpersActual
open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafObjActual
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafStrongActual
open LeanFormal.IUT.XiFPaper.S3128OfHObjectActual
open LeanFormal.IUT.XiFPaper.S3128OfHHomLemmasActual
open LeanFormal.IUT.XiFPaper.S3128PrestackActual
open LeanFormal.IUT.XiFPaper.S3128OfHMapActual
open LeanFormal.IUT.XiFPaper.S3128OfHHelpersActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.S3128StrongBaseChangeFunctorOfHActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F} {U : SchemeOverField F}
variable (H : Over U ⥤ Over U)
variable (hH : ∀ V : (Over U)ᵒᵖ, H.op.obj V ≅ V)

def S3128StrongBaseChangeObjOfH
    (A : S3128ZMod2QuotientSheafObj (F:=F) (X:=X) U) :
    S3128ZMod2QuotientSheafObj (F:=F) (X:=X) U :=
  S3128BaseChangeOfH' H hH A

def S3128StrongBaseChangeMapOfH
    {A B : S3128ZMod2QuotientSheafObj (F:=F) (X:=X) U}
    (φ : S3128StrongHom A B) :
    S3128StrongHom
      (S3128StrongBaseChangeObjOfH H hH A)
      (S3128StrongBaseChangeObjOfH H hH B) :=
  S3128OfHHom H hH φ

noncomputable def S3128StrongBaseChangeFunctorOfH :
    S3128ZMod2QuotientSheafObj (F:=F) (X:=X) U ⥤
      S3128ZMod2QuotientSheafObj (F:=F) (X:=X) U where
  obj := S3128StrongBaseChangeObjOfH H hH
  map := S3128StrongBaseChangeMapOfH H hH
  map_id A := by
    apply S3128StrongHom.ext
    · apply Iso.ext
      apply NatTrans.ext
      funext V
      rfl
    · apply heq_of_eq
      funext V p
      apply Iso.ext
      change
        ((S3128OfHHMap H hH V).mapIso
          ((S3128StrongHom.id A).mapCompat
            (H.op.obj V) p)).hom =
        ((S3128StrongHom.id
          (S3128StrongBaseChangeObjOfH H hH A)).mapCompat V p).hom
      rw [S3128StrongHom.id_mapCompat]
      rw [S3128StrongHom.id_mapCompat]
      change
        (S3128OfHHMap H hH V).map
          (𝟙 (A.mapPoint (H.op.obj V) p)) =
        𝟙 ((S3128OfHHMap H hH V).obj (A.mapPoint (H.op.obj V) p))
      exact (S3128OfHHMap H hH V).map_id _
  map_comp {A B C} (φ : A ⟶ B) (ψ : B ⟶ C) := by
    apply S3128StrongHom.ext
    · change S3128WhiskerLeftIso H.op (φ.pointsIso ≪≫ ψ.pointsIso) =
        S3128WhiskerLeftIso H.op φ.pointsIso ≪≫
          S3128WhiskerLeftIso H.op ψ.pointsIso
      exact S3128WhiskerLeftIso_trans H.op φ.pointsIso ψ.pointsIso
    · apply heq_of_eq
      funext V p
      apply Iso.ext
      change
        ((S3128OfHHMap H hH V).mapIso
          (((S3128StrongHom.comp φ ψ).mapCompat) (H.op.obj V) p)).hom =
        (((S3128OfHHMap H hH V).mapIso
            (ψ.mapCompat (H.op.obj V) (φ.pointsIso.hom.app (H.op.obj V) p))).trans
          ((S3128OfHHMap H hH V).mapIso (φ.mapCompat (H.op.obj V) p))).hom
      rw [S3128StrongHom.comp_mapCompat]
      change
        ((S3128OfHHMap H hH V).mapIso
          ((ψ.mapCompat (H.op.obj V) (φ.pointsIso.hom.app (H.op.obj V) p)).trans
            (φ.mapCompat (H.op.obj V) p))).hom =
        (((S3128OfHHMap H hH V).mapIso
            (ψ.mapCompat (H.op.obj V) (φ.pointsIso.hom.app (H.op.obj V) p))).trans
          ((S3128OfHHMap H hH V).mapIso (φ.mapCompat (H.op.obj V) p))).hom
      rw [S3128OfHHMap_mapIso_trans]

#check S3128StrongBaseChangeObjOfH
#check S3128StrongBaseChangeMapOfH
end LeanFormal.IUT.XiFPaper.S3128StrongBaseChangeFunctorOfHActual