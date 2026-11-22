import tmp.sheaf.xif.paper.S3127G2ActionBaseActual
import tmp.sheaf.xif.paper.S3127GammaRAlgebraActual
import tmp.sheaf.xif.paper.S3127GammaActionActual
import tmp.sheaf.xif.paper.S3127GammaCompActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127GammaCompActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaAutAlgHomActual
variable {l : PrimeGeFive} {G : Type} [Group G]

noncomputable def S3127G2GammaAutAlgHom
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g : G) :
    let R := S1348CoordinateRing l
    letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
    letI := gammaMulSemiringAction act.act
    Scheme.Γ.obj (Opposite.op A.obj.left.left) →ₐ[R]
      Scheme.Γ.obj (Opposite.op A.obj.left.left) := by
  let R := S1348CoordinateRing l
  letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
  letI := gammaMulSemiringAction act.act
  exact
    { toRingHom := (gammaAut (act.act g)).toRingHom
      commutes' := by
        intro c
        exact S3127FixesAlgebraMapOf A act g c }

#check S3127G2GammaAutAlgHom
end LeanFormal.IUT.XiFPaper.S3127G2GammaAutAlgHomActual
end