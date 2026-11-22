import tmp.sheaf.xif.paper.S3127G2ActionBaseActual
import tmp.sheaf.xif.paper.S3127GammaActionActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaAutSymmActual
variable {l : PrimeGeFive} {G : Type} [Group G]

theorem S3127G2GammaAut_symm
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g : G) :
    gammaAut (act.act g).symm = (gammaAut (act.act g)).symm := by
  rfl

#check S3127G2GammaAut_symm
end LeanFormal.IUT.XiFPaper.S3127G2GammaAutSymmActual
end