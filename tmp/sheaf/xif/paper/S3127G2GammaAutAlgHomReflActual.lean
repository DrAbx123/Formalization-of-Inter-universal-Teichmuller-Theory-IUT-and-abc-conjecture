import tmp.sheaf.xif.paper.S3127G2GammaAutAlgHomActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127GammaCompActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaAutAlgHomActual
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaAutAlgHomReflActual
variable {l : PrimeGeFive} {G : Type} [Group G]

theorem S3127G2GammaAutAlgHom_one
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) :
    let R := S1348CoordinateRing l
    letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
    letI := gammaMulSemiringAction act.act
    (S3127G2GammaAutAlgHom A act 1) =
      AlgHom.id R (Scheme.Γ.obj (Opposite.op A.obj.left.left)) := by
  ext x
  rfl

#check S3127G2GammaAutAlgHom_one
end LeanFormal.IUT.XiFPaper.S3127G2GammaAutAlgHomReflActual
end