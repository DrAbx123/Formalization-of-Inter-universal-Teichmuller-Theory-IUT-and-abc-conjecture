import tmp.sheaf.xif.paper.S3127G2QFullUnitActual
import tmp.sheaf.xif.paper.S3127G2TargetActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2QFullUnitActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2QFullUnitConsumerActualAdapted
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G]

structure S3127G2QFullUnitConsumer  : Type 2 where
  unitCover : FiniteEtaleCover (S1419AffineScheme l)
  targetCover : FiniteEtaleCover (S1419AffineScheme l)
  unitCover_eq : unitCover = S3127G2QFullUnit A act
  targetCover_eq : targetCover = S3127G2QFull A act

noncomputable def S3127G2QFullUnitConsumer.of : S3127G2QFullUnitConsumer A act where
  unitCover := S3127G2QFullUnit A act
  targetCover := S3127G2QFull A act
  unitCover_eq := rfl
  targetCover_eq := rfl

#check S3127G2QFullUnitConsumer
#check S3127G2QFullUnitConsumer.of
end LeanFormal.IUT.XiFPaper.S3127G2QFullUnitConsumerActualAdapted
end
