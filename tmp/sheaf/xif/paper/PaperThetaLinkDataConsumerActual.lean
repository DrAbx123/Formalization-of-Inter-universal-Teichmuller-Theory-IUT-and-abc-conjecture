import tmp.sheaf.xif.paper.PaperThetaLinkDataActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperThetaLinkDataConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperThetaLinkDataActual
open LeanFormal.IUT.Theorem311Source.IPLAPTDataActual

universe uv

variable {V : Type uv}

theorem selfPaperThetaLinkData_ipl_projection (envStrip : FPrimeStrip V) :
    (selfPaperThetaLinkData envStrip).ipl = selfIplActual envStrip := rfl

theorem selfPaperThetaLinkData_kummerEvaluation_projection (envStrip : FPrimeStrip V) :
    (selfPaperThetaLinkData envStrip).kummerEvaluation =
      selfKummerEvaluationActual envStrip := rfl

theorem selfPaperThetaLinkData_inputLink_projection (envStrip : FPrimeStrip V) :
    (selfPaperThetaLinkData envStrip).inputLink =
      (selfIplActual envStrip).inputLink := rfl

theorem selfPaperThetaLinkData_composite_projection (envStrip : FPrimeStrip V) :
    (selfPaperThetaLinkData envStrip).ipl.composite =
      (selfIplActual envStrip).composite := rfl

theorem selfPaperThetaLinkData_ipl_factorization_consumer (envStrip : FPrimeStrip V) :
    (selfPaperThetaLinkData envStrip).ipl.inputLink =
      (selfPaperThetaLinkData envStrip).ipl.composite := by
  rw [selfPaperThetaLinkData_ipl_projection]
  exact (selfIplActual envStrip).factorization

theorem selfPaperThetaLinkData_kummerEvaluation_commutes_consumer (envStrip : FPrimeStrip V) :
    (selfPaperThetaLinkData envStrip).kummerEvaluation.square.domainExpression =
      (selfPaperThetaLinkData envStrip).kummerEvaluation.square.codomainExpression := by
  rw [selfPaperThetaLinkData_kummerEvaluation_projection]
  exact KummerEvaluationActual.domainExpression_eq_codomainExpression
    (selfKummerEvaluationActual envStrip)

#check selfPaperThetaLinkData_ipl_factorization_consumer
#check selfPaperThetaLinkData_kummerEvaluation_commutes_consumer

end LeanFormal.IUT.XiFPaper.PaperThetaLinkDataConsumerActual

end