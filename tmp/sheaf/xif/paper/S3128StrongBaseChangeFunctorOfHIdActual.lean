import tmp.sheaf.xif.paper.S3128StrongBaseChangeFunctorOfHActual
import tmp.sheaf.xif.paper.S3128CanonicalHEndActual
noncomputable section
open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafObjActual
open LeanFormal.IUT.XiFPaper.S3128CanonicalHEndActual
open LeanFormal.IUT.XiFPaper.S3128StrongBaseChangeFunctorOfHActual
namespace LeanFormal.IUT.XiFPaper.S3128StrongBaseChangeFunctorOfHIdActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F} {U : SchemeOverField F}

noncomputable def S3128StrongBaseChangeFunctorOfHId :
    S3128ZMod2QuotientSheafObj (F:=F) (X:=X) U ⥤
      S3128ZMod2QuotientSheafObj (F:=F) (X:=X) U :=
  S3128StrongBaseChangeFunctorOfH (Over.map (𝟙 U))
    (fun V => S3128CanonicalMapIdIso (U := U) V)

#check S3128StrongBaseChangeFunctorOfHId
end LeanFormal.IUT.XiFPaper.S3128StrongBaseChangeFunctorOfHIdActual
end
