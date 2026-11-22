import tmp.sheaf.xif.paper.S3128CanonicalMapIdNatActual
import tmp.sheaf.xif.paper.S3128OfHMapActual
open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafObjActual
open LeanFormal.IUT.XiFPaper.S3128CanonicalMapIdNatActual
open LeanFormal.IUT.XiFPaper.S3128CanonicalHEndActual
open LeanFormal.IUT.XiFPaper.S3128OfHMapActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.S3128QuotientMapPointCoherenceActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F} {U : SchemeOverField F}

/-- Coherence of `mapPoint` along the canonical identity base-change iso.
This is the missing structure needed for the OfHId ≅ 𝟭 mapId. -/
structure S3128MapPointCoherence
    (A : S3128ZMod2QuotientSheafObj (F:=F) (X:=X) U) where
  canon :
    ∀ (V : (Over U)ᵒᵖ)
      (p : A.points.obj ((Over.map (𝟙 U)).op.obj V)),
      (S3128OfHHMap (Over.map (𝟙 U))
        (fun V => S3128CanonicalMapIdIso (U := U) V) V).obj
        (A.mapPoint ((Over.map (𝟙 U)).op.obj V) p)
      ≅ A.mapPoint V p

#check S3128MapPointCoherence
end LeanFormal.IUT.XiFPaper.S3128QuotientMapPointCoherenceActual