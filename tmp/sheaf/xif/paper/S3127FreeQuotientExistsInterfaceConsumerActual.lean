import tmp.sheaf.xif.paper.S3127FreeQuotientExistsInterfaceActual
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
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127FreeQuotientExistsInterfaceConsumerActual
variable {l : PrimeGeFive}

/-- Consumer projection: paper input gives, for each finite group and cover,
a quotient target with its universal property. -/
theorem S3127FreeQuotientExists_paperInput_target
    (h : S3127FreeQuotientPaperInput (l := l))
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (A : S3127FiniteEtaleOverKFull l) :
    ∃ T : S3127FreeQuotientTarget A G, S3127QuotientUniversal T :=
  S3127FreeQuotientExists_of_freeAction_and_universalData h G A

/-- Consumer projection for the quotient object itself. -/
theorem S3127FreeQuotientExists_paperInput_quotient
    (h : S3127FreeQuotientPaperInput (l := l))
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (A : S3127FiniteEtaleOverKFull l) :
    ∃ q : S3127FiniteEtaleOverKFull l, Nonempty (A ⟶ q) :=
  let ⟨T, _⟩ := S3127FreeQuotientExists_paperInput_target h G A
  ⟨T.quotientObj, ⟨T.quotientMap⟩⟩

/-- Downstream scope marker: the G2 theorem is consumed only through paper input. -/
theorem S3127FreeQuotientExists_interface_scope
    (h : S3127FreeQuotientPaperInput (l := l)) :
    S3127FreeQuotientExists (l := l) :=
  S3127FreeQuotientExists_of_freeAction_and_universalData h

#check S3127FreeQuotientExists_paperInput_target
#check S3127FreeQuotientExists_paperInput_quotient
#check S3127FreeQuotientExists_interface_scope
end LeanFormal.IUT.XiFPaper.S3127FreeQuotientExistsInterfaceConsumerActual
end