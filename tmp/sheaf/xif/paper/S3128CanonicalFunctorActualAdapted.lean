import tmp.sheaf.xif.paper.S3128CanonicalHEndActual
import tmp.sheaf.xif.paper.S3128OfHHomLemmasActual
import tmp.sheaf.xif.paper.S3128OfHHelpersActual
open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafObjActual
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafStrongActual
open LeanFormal.IUT.XiFPaper.S3128OfHObjectActual
open LeanFormal.IUT.XiFPaper.S3128OfHMapActual
open LeanFormal.IUT.XiFPaper.S3128OfHHomLemmasActual
open LeanFormal.IUT.XiFPaper.S3128OfHHelpersActual
open LeanFormal.IUT.XiFPaper.S3128CanonicalHEndActual
open LeanFormal.IUT.XiFPaper.S3128PrestackActual
noncomputable section
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.S3128CanonicalFunctorActualAdapted
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F} {U : SchemeOverField F}

noncomputable def S3128StrongBaseChangeFunctorOfHCanon
    (A : S3128CanonicalHEnd U) :
    S3128ZMod2QuotientSheafObj (F:=F) (X:=X) U ⥤
      S3128ZMod2QuotientSheafObj (F:=F) (X:=X) U where
  obj X := S3128BaseChangeOfH' A.H A.hH X
  map φ := S3128OfHHom A.H A.hH φ
  map_id X := by
    apply S3128StrongHom.ext
    · change
        S3128WhiskerLeftIso A.H.op (Iso.refl X.points) =
        Iso.refl
          (S3128BaseChangeOfH' A.H A.hH X).points
      rw [S3128WhiskerLeftIso_refl]
      rfl
    · apply heq_of_eq
      funext V p
      apply Iso.ext
      dsimp [S3128BaseChangeOfH']
      change
        ((S3128OfHHMap A.H A.hH V).mapIso
          ((S3128StrongHom.id X).mapCompat
            (A.H.op.obj V) p)).hom =
        ((S3128StrongHom.id
          (S3128BaseChangeOfH' A.H A.hH X)).mapCompat V p).hom
      rw [S3128StrongHom.id_mapCompat]
      simp only [S3128StrongHom.id, Iso.refl_hom,
        NatTrans.id_app]
      rw [S3128OfHHMap_mapIso_refl]
  map_comp {X Y Z} (φ : X ⟶ Y) (ψ : Y ⟶ Z) := by
    apply S3128StrongHom.ext
    · change
        S3128WhiskerLeftIso A.H.op
          (S3128StrongHom.comp
            (show S3128StrongHom X Y from φ)
            (show S3128StrongHom Y Z from ψ)).pointsIso =
        (S3128StrongHom.comp
          (S3128OfHHom A.H A.hH φ)
          (S3128OfHHom A.H A.hH ψ)).pointsIso
      dsimp [S3128StrongHom.comp]
      rw [S3128WhiskerLeftIso_trans]
    · apply heq_of_eq
      funext V p
      apply Iso.ext
      dsimp [S3128OfHHom, S3128StrongHom.comp]
      rw [S3128StrongHom.comp_mapCompat]
      rw [S3128OfHHMap_mapIso_trans]
      rfl

#check S3128StrongBaseChangeFunctorOfHCanon
end LeanFormal.IUT.XiFPaper.S3128CanonicalFunctorActualAdapted