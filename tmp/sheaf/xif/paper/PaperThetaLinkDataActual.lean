import tmp.sheaf.xif.paper.PaperXiFUnconditional
import tmp.sheaf.xif.paper.IPLAPTDataActual

/-!
# Actual PaperThetaLinkData from the self IPL/Kummer-evaluation data

This file instantiates the paper-level record

  PaperThetaLinkData intermediateStrip gauStrip envStrip coricEnvStrip
    qPilotStrip upperLeft upperRight lowerLeft lowerRight

with all nine strips equal to one canonical envStrip, using
IPLAPTDataActual.selfIplActual and IPLAPTDataActual.selfKummerEvaluationActual
on the actual product group SelfGroup envStrip.

This is the identity/trivial-source specialization explicitly permitted by the
task. The IPL factorization and the Kummer-evaluation two-path equality are the
actual equalities of those records. The non-trivial paper strip
identifications (intermediate/gau/coric/q-pilot/upper/lower distinct from env)
are NOT made; they remain the exact missing strip data. No toy/True/PUnit/
axiom/sorry is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace XiFPaper
namespace PaperThetaLinkDataActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.Theorem311Source.IPLAPTDataActual

universe uv

variable {V : Type uv}

/-- Actual paper Theta-link data with all strips equal to the canonical
envStrip. -/
noncomputable def selfPaperThetaLinkData (envStrip : FPrimeStrip V) :
    PaperThetaLinkData (G := SelfGroup envStrip)
      envStrip envStrip envStrip envStrip envStrip
      envStrip envStrip envStrip envStrip where
  ipl := selfIplActual envStrip
  kummerEvaluation := selfKummerEvaluationActual envStrip

/-- The IPL input link of the self paper Theta-link data is the actual self IPL
input link. -/
theorem selfPaperThetaLinkData_inputLink
    (envStrip : FPrimeStrip V) :
    (selfPaperThetaLinkData envStrip).inputLink =
      (selfIplActual envStrip).inputLink := rfl

/-- The actual IPL factorization carried by the self paper Theta-link data. -/
theorem selfPaperThetaLinkData_ipl_factorization
    (envStrip : FPrimeStrip V) :
    (selfPaperThetaLinkData envStrip).ipl.inputLink =
      (selfPaperThetaLinkData envStrip).ipl.composite :=
  (selfPaperThetaLinkData envStrip).ipl_factorization

/-- The actual Kummer-evaluation two-path equality carried by the self paper
Theta-link data. -/
theorem selfPaperThetaLinkData_kummerEvaluation_commutes
    (envStrip : FPrimeStrip V) :
    (selfPaperThetaLinkData envStrip).kummerEvaluation.square.domainExpression =
      (selfPaperThetaLinkData envStrip).kummerEvaluation.square.codomainExpression :=
  (selfPaperThetaLinkData envStrip).kummerEvaluation_commutes

/-- The actual input link of the self paper Theta-link data, as a strip
equivalence. -/
noncomputable def selfPaperThetaLinkInputLink
    (envStrip : FPrimeStrip V) :
    FPrimeStripEquiv envStrip envStrip :=
  (selfPaperThetaLinkData envStrip).inputLink

end PaperThetaLinkDataActual
end XiFPaper
end LeanFormal.IUT
end
