import tmp.sheaf.xif.paper.ActualPaperThetaLinkActual
import tmp.sheaf.xif.paper.LogKummerCorrespondenceFromSource

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperThetaLinkConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ActualPaperThetaLinkActual

universe uv ua upi umon ui

variable {V : Type uv} {l : PrimeGeFive}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

theorem actualPaperThetaLinkData_ipl_projection :
    (actualPaperThetaLinkData).ipl = actualIPLData (I := I) := rfl

theorem actualPaperThetaLinkData_kummerEvaluation_projection :
    (actualPaperThetaLinkData).kummerEvaluation =
      actualPaperKummerEvaluation (I := I) := rfl

theorem actualPaperThetaLinkData_ipl_factorization_consumer :
    (actualPaperThetaLinkData).ipl.inputLink =
      (actualPaperThetaLinkData).ipl.composite := by
  rw [actualPaperThetaLinkData_ipl_projection]
  exact (actualIPLData (I := I)).factorization

theorem actualPaperKummerEvaluation_square_consumer :
    (actualPaperKummerEvaluation).square.domainExpression =
      (actualPaperKummerEvaluation).square.codomainExpression :=
  KummerEvaluationActual.domainExpression_eq_codomainExpression
    (actualPaperKummerEvaluation)

theorem actualPaperThetaLinkData_kummerEvaluation_commutes_consumer :
    (actualPaperThetaLinkData).kummerEvaluation.square.domainExpression =
      (actualPaperThetaLinkData).kummerEvaluation.square.codomainExpression := by
  rw [actualPaperThetaLinkData_kummerEvaluation_projection]
  exact actualPaperKummerEvaluation_square_consumer (I := I)

#check actualPaperThetaLinkData_ipl_factorization_consumer
#check actualPaperThetaLinkData_kummerEvaluation_commutes_consumer

end LeanFormal.IUT.XiFPaper.PaperThetaLinkConsumerActual

end