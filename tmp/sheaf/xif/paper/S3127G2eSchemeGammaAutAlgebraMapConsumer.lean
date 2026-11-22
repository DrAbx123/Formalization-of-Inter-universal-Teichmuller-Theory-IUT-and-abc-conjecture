import tmp.sheaf.xif.paper.S3127G2eSchemeGammaAutConsumer
import tmp.sheaf.xif.paper.S3127G2eSchemeAlgebraMapConsumer
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
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeAlgebraMapConsumer
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutAlgebraMapConsumer
variable {l : PrimeGeFive} {G : Type} [Group G]

theorem S3127G2eSchemeGammaAut_hom_comp
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g : G) :
    let R := S1348CoordinateRing l
    letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
    letI := gammaMulSemiringAction act.act
    (S3127G2eSchemeOfGammaAut A act g).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R (Scheme.Γ.obj (Opposite.op A.obj.left.left)))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Scheme.Γ.obj (Opposite.op A.obj.left.left)))) := by
  letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
  letI := gammaMulSemiringAction act.act
  exact S3127G2eScheme_hom_comp (R := S1348CoordinateRing l)
    A.obj.left.left
    (algebraMap (S1348CoordinateRing l)
      (Scheme.Γ.obj (Opposite.op A.obj.left.left)))
    (gammaAut (act.act g))
    (fun c => S3127FixesAlgebraMapOf A act g c)

#check S3127G2eSchemeGammaAut_hom_comp
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutAlgebraMapConsumer
end