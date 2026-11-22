import tmp.sheaf.xif.paper.S3127G2ActionBaseActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2OverRDataActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)

structure S3127G2OverRData : Type where
  overR : ∀ g : G, (act.act g).hom ≫ A.obj.hom.left = A.obj.hom.left
  overR_inv : ∀ g : G,
    (act.act g).symm.hom ≫ A.obj.hom.left = A.obj.hom.left

noncomputable def S3127G2OverRData.of : S3127G2OverRData A act where
  overR := act.overR
  overR_inv := S3127OverRAction_inv A act

#check S3127G2OverRData
#check S3127G2OverRData.of
end LeanFormal.IUT.XiFPaper.S3127G2OverRDataActual
end
