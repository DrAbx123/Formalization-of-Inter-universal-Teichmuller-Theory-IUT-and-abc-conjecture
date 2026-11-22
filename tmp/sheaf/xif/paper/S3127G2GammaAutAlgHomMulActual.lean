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
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaAutAlgHomMulActual
variable {l : PrimeGeFive} {G : Type} [Group G]

theorem S3127G2GammaAutAlgHom_mul
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g h : G) :
    let R := S1348CoordinateRing l
    letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
    letI := gammaMulSemiringAction act.act
    (S3127G2GammaAutAlgHom A act (g * h)) =
      (S3127G2GammaAutAlgHom A act g).comp
        (S3127G2GammaAutAlgHom A act h) := by
  ext x
  rfl

#check S3127G2GammaAutAlgHom_mul
end LeanFormal.IUT.XiFPaper.S3127G2GammaAutAlgHomMulActual
end