import tmp.sheaf.xif.paper.S3128StrongBaseChangeFunctorOfHIdActual
import tmp.sheaf.xif.paper.S3128MapPointCoherenceActual
open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafObjActual
open LeanFormal.IUT.XiFPaper.S3128StrongBaseChangeFunctorOfHIdActual
open LeanFormal.IUT.XiFPaper.S3128QuotientMapPointCoherenceActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.S3128OfHIdTargetsActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F} {U : SchemeOverField F}

def S3128OfHIdMapIdTarget : Prop :=
  Nonempty
    (S3128StrongBaseChangeFunctorOfHId (F:=F) (X:=X) (U:=U)
      ≅ 𝟭 (S3128ZMod2QuotientSheafObj (F:=F) (X:=X) U))

def S3128MapPointCoherenceTarget : Prop :=
  ∀ A : S3128ZMod2QuotientSheafObj (F:=F) (X:=X) U,
    Nonempty (S3128MapPointCoherence A)

#check S3128OfHIdMapIdTarget
#check S3128MapPointCoherenceTarget
end LeanFormal.IUT.XiFPaper.S3128OfHIdTargetsActual