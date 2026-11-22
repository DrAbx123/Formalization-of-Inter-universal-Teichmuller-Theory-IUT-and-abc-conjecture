import tmp.sheaf.xif.paper.S3127G2TargetActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2QuotientObjActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2QuotientObjActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2QFullDataActualAdapted
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]

structure S3127G2QFullData  : Type 2 where
  quotientBase : FiniteEtaleCover (S1419AffineScheme l)
  quotientObj : S3127FiniteEtaleOverKFull l
  quotientObj_eq : quotientObj = S3127G2QuotientObj quotientBase
  quotientMap : A ⟶ quotientObj

noncomputable def S3127G2QFullData.of : S3127G2QFullData A act where
  quotientBase := S3127G2QFull A act
  quotientObj := S3127G2QuotientObj (S3127G2QFull A act)
  quotientObj_eq := rfl
  quotientMap := S3127G2QuotientMap A act

#check S3127G2QFullData
#check S3127G2QFullData.of
end LeanFormal.IUT.XiFPaper.S3127G2QFullDataActualAdapted
end
