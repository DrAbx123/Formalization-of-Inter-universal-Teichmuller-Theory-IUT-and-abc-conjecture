import tmp.sheaf.xif.paper.S3127G2UniversalDataActual
import tmp.sheaf.xif.paper.S3127G2TargetActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2UniversalDataConsumerActual
variable {l : PrimeGeFive} {G : Type} [Group G] [Fintype G]
variable {A : S3127FiniteEtaleOverKFull l} (T : S3127FreeQuotientTarget A G)

structure S3127G2UniversalDataConsumer
    (A : S3127FiniteEtaleOverKFull l)
    (T : S3127FreeQuotientTarget A G) : Type 2 where
  data : S3127G2UniversalData A T
  universal : S3127QuotientUniversal T
  universal_eq : universal = S3127QuotientUniversal_of_data T data

noncomputable def S3127G2UniversalDataConsumer.of
    (P : S3127G2UniversalData A T) : S3127G2UniversalDataConsumer A T where
  data := P
  universal := S3127QuotientUniversal_of_data T P
  universal_eq := rfl

#check S3127G2UniversalDataConsumer
#check S3127G2UniversalDataConsumer.of
end LeanFormal.IUT.XiFPaper.S3127G2UniversalDataConsumerActual
end
