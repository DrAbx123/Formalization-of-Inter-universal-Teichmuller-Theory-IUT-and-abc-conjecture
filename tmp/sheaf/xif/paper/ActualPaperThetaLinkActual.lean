import tmp.sheaf.xif.paper.PaperXiFUnconditional
import tmp.sheaf.xif.paper.ThetaLinkIPLFactorizationActual

/-!
# Actual PaperThetaLinkData from concrete IPL and Kummer-evaluation data

Uses the actual `actualIPLData` of `LogKummerCorrespondenceFromSource` and the
actual four-corner square of `ThetaLinkIPLFactorizationActual`.  No arbitrary
strips, actions, True/PUnit, axioms or sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ActualPaperThetaLinkActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ThetaLinkIPLFactorizationActual

universe uv ua upi umon ui

variable {V : Type uv} {l : PrimeGeFive}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The actual four-corner Kummer-evaluation record of the concrete square. -/
noncomputable def actualPaperKummerEvaluation :
    KummerEvaluationActual (G := ActualKummerGroup (I := I))
      (S00 (I := I)) (S01 (I := I)) (S10 (I := I)) (S11 (I := I)) where
  square := actualSquare (I := I)

/-- The actual IPL/Kummer-evaluation Theta-link data at the concrete IPL strips. -/
noncomputable def actualPaperThetaLinkData :
    PaperThetaLinkData (G := ActualKummerGroup (I := I))
      (intermediateStrip := iplIntermediateStrip (I := I))
      (gauStrip := iplGauStrip (I := I))
      (envStrip := iplEnvStrip (I := I))
      (coricEnvStrip := iplCoricEnvStrip (I := I))
      (qPilotStrip := iplQPilotStrip (I := I))
      (upperLeft := S00 (I := I)) (upperRight := S01 (I := I))
      (lowerLeft := S10 (I := I)) (lowerRight := S11 (I := I)) where
  ipl := actualIPLData (I := I)
  kummerEvaluation := actualPaperKummerEvaluation (I := I)

@[simp] theorem actualPaperThetaLinkData_ipl :
    (actualPaperThetaLinkData (I := I)).ipl = actualIPLData (I := I) := rfl

@[simp] theorem actualPaperThetaLinkData_kummerEvaluation :
    (actualPaperThetaLinkData (I := I)).kummerEvaluation =
      actualPaperKummerEvaluation (I := I) := rfl

theorem actualPaperThetaLinkData_inputLink_eq_composite (I : OriginalInput l V) :
    (actualPaperThetaLinkData (I := I)).ipl.inputLink =
      (actualPaperThetaLinkData (I := I)).ipl.composite :=
  (actualPaperThetaLinkData (I := I)).ipl_factorization

theorem actualPaperThetaLinkData_kummerEvaluation_commutes (I : OriginalInput l V) :
    (actualPaperThetaLinkData (I := I)).kummerEvaluation.square.domainExpression =
      (actualPaperThetaLinkData (I := I)).kummerEvaluation.square.codomainExpression :=
  (actualPaperThetaLinkData (I := I)).kummerEvaluation_commutes

#print axioms actualPaperThetaLinkData
#print axioms actualPaperThetaLinkData_inputLink_eq_composite
#print axioms actualPaperThetaLinkData_kummerEvaluation_commutes

end LeanFormal.IUT.XiFPaper.ActualPaperThetaLinkActual
end
