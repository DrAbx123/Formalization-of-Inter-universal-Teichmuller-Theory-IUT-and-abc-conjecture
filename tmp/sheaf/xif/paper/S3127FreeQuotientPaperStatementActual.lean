import tmp.sheaf.xif.paper.S3127FreeQuotientExistsInterfaceActual
import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsOfData1Actual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientExistsInterfaceActual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsOfData1Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127FreeQuotientPaperStatementActual
variable {l : PrimeGeFive}

/-- Named paper statement (conditional form): free action + universal data implies G2 existence. -/
def S3127G2PaperStatement : Prop :=
  S3127FreeQuotientPaperInput (l := l) → S3127FreeQuotientExists (l := l)

/-- The named paper statement holds, via the explicit interface. -/
theorem S3127G2PaperStatement_holds : S3127G2PaperStatement (l := l) :=
  S3127FreeQuotientExists_of_freeAction_and_universalData

/-- Cross-check: the same paper input also feeds the OfData1 route. -/
theorem S3127FreeQuotientExists_of_paperInput_via_data
    (h : S3127FreeQuotientPaperInput (l := l)) :
    S3127FreeQuotientExists (l := l) :=
  S3127FreeQuotientExists_of_data h

#check S3127G2PaperStatement
#check S3127G2PaperStatement_holds
#check S3127FreeQuotientExists_of_paperInput_via_data
end LeanFormal.IUT.XiFPaper.S3127FreeQuotientPaperStatementActual
end