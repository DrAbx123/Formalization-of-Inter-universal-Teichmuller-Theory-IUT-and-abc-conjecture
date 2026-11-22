import tmp.sheaf.xif.paper.ConcretePaperUnconditionalDataActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ConcreteThetaLinkConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.Theorem311Source.IPLAPTDataActual
open LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataActual
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual

universe ua upi umon ui

variable {l : PrimeGeFive}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}

theorem concreteThetaLinkData_ipl_projection :
    (concreteThetaLinkData (l := l) (I := I)).ipl =
      selfIplActual (concreteQPilotStrip (l := l)) := rfl

theorem concreteThetaLinkData_kummerEvaluation_projection :
    (concreteThetaLinkData (l := l) (I := I)).kummerEvaluation =
      selfKummerEvaluationActual (concreteQPilotStrip (l := l)) := rfl

theorem concreteThetaLinkData_inputLink_projection :
    (concreteThetaLinkData (l := l) (I := I)).inputLink =
      (selfIplActual (concreteQPilotStrip (l := l))).inputLink := rfl

theorem concreteThetaLinkData_ipl_factorization :
    (concreteThetaLinkData (l := l) (I := I)).ipl.inputLink =
      (concreteThetaLinkData (l := l) (I := I)).ipl.composite := by
  rw [concreteThetaLinkData_ipl_projection]
  exact (selfIplActual (concreteQPilotStrip (l := l))).factorization

theorem concreteThetaLinkData_kummerEvaluation_commutes :
    (concreteThetaLinkData (l := l) (I := I)).kummerEvaluation.square.domainExpression =
      (concreteThetaLinkData (l := l) (I := I)).kummerEvaluation.square.codomainExpression := by
  rw [concreteThetaLinkData_kummerEvaluation_projection]
  exact KummerEvaluationActual.domainExpression_eq_codomainExpression
    (selfKummerEvaluationActual (concreteQPilotStrip (l := l)))

#check concreteThetaLinkData_ipl_factorization
#check concreteThetaLinkData_kummerEvaluation_commutes

end LeanFormal.IUT.XiFPaper.ConcreteThetaLinkConsumerActual

end