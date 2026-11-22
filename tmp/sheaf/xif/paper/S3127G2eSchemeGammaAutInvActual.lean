import tmp.sheaf.xif.paper.S3127G2eSchemeGammaAutConsumer
import tmp.sheaf.xif.paper.S3127G2eSchemeInvConsumer
import tmp.sheaf.xif.paper.S3127G2GammaAutInvApplyActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127GammaCompActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeInvConsumer
open LeanFormal.IUT.XiFPaper.S3127G2GammaAutInvApplyActual
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutInvActual
variable {l : PrimeGeFive} {G : Type} [Group G]

theorem S3127G2eSchemeGammaAut_inv
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g : G) :
    (S3127G2eSchemeOfGammaAut A act g).inv =
      S3127G2eSchemeOfGammaAut A act g⁻¹ := by
  rw [S3127G2eScheme_inv]
  congr 1
  rw [S3127G2GammaAut_symm_general]
  rw [act.act.map_inv]

#check S3127G2eSchemeGammaAut_inv
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutInvActual
end