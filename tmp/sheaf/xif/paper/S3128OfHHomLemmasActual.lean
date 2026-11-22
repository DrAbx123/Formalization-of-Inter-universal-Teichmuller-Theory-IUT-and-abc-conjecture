import tmp.sheaf.xif.paper.S3128OfHObjectActual
open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafObjActual
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafStrongActual
namespace LeanFormal.IUT.XiFPaper.S3128OfHHomLemmasActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F} {U : SchemeOverField F}

theorem S3128StrongHom.id_mapCompat
    (A : S3128ZMod2QuotientSheafObj (F:=F) (X:=X) U) :
    (S3128StrongHom.id A).mapCompat = fun V p => Iso.refl _ := rfl

theorem S3128StrongHom.comp_mapCompat
    {A B C : S3128ZMod2QuotientSheafObj (F:=F) (X:=X) U}
    (φ : S3128StrongHom A B) (ψ : S3128StrongHom B C) :
    (S3128StrongHom.comp φ ψ).mapCompat =
      fun V p =>
        (ψ.mapCompat V ((φ.pointsIso.hom.app V) p)).trans
          (φ.mapCompat V p) := rfl

#check S3128StrongHom.id_mapCompat
#check S3128StrongHom.comp_mapCompat
end LeanFormal.IUT.XiFPaper.S3128OfHHomLemmasActual