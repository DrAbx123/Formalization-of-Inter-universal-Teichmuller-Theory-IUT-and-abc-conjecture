import tmp.sheaf.xif.paper.S3127G2TargetActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2QuotientObjActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientObjActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2QuotientDataActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]

structure S3127G2QuotientData
    (A : S3127FiniteEtaleOverKFull l)
    (act : S3127OverRAction A G) : Type where
  quotientObj : S3127FiniteEtaleOverKFull l
  quotientMap : A ⟶ quotientObj
  invariant : ∀ g : G, S3127G2Action A act g ≫ quotientMap = quotientMap

noncomputable def S3127G2QuotientData.of
    (hInv : ∀ g : G, S3127G2Action A act g ≫ S3127G2QuotientMap A act =
      S3127G2QuotientMap A act) : S3127G2QuotientData A act where
  quotientObj := S3127G2QuotientObj (S3127G2QFull A act)
  quotientMap := S3127G2QuotientMap A act
  invariant := hInv

#check S3127G2QuotientData
#check S3127G2QuotientData.of
end LeanFormal.IUT.XiFPaper.S3127G2QuotientDataActual
end
