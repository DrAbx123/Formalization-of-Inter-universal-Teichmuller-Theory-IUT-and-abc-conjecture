import tmp.sheaf.xif.paper.S3127G2QFullUnitActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127FreeQuotientActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.XiFPaper.S3127G2QFullUnitActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2QFullUnitDataActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G]

structure S3127G2QFullUnitData
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) : Type 2 where
  cover : FiniteEtaleCover (S1419AffineScheme l)
  cover_eq : cover = S3127G2QFullUnit A act

noncomputable def S3127G2QFullUnitData.of : S3127G2QFullUnitData A act where
  cover := S3127G2QFullUnit A act
  cover_eq := rfl

#check S3127G2QFullUnitData
#check S3127G2QFullUnitData.of
end LeanFormal.IUT.XiFPaper.S3127G2QFullUnitDataActual
end
