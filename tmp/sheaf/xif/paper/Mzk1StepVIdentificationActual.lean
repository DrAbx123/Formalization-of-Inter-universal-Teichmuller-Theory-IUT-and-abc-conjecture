/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1StepVVolumeUpperActual
import Mathlib.Tactic

/-! # A816 hull: object identification `V = stepVExpr` and paper dictionary

Target: `V = stepVExpr floorTerm sumB logp` and the paper dictionary
`lambda/sumDiff <-> logd+logf = logdf`, with absolute `C0`.

Status: our actual paper-normalized hull volumes (`thetaScaledLog`,
`thetaPilotHullLogVolumeReal`, `s1915ClosedForm`) live on the S1902/C3
carriers; lana's `stepV` lives on the `InitialThetaData`/`hull(vcI)` carrier.
No green theorem identifies them, so the object identification remains an
explicit hypothesis.  The conditional assembly is proved. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1StepVIdentificationActual

open LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeUpperActual

/-- Object identification + Step-V bound + box bound, as explicit data. -/
structure StepVDictionary where
  V : ℝ
  floorTerm : ℝ
  sumB : ℝ
  logp : ℝ
  lambda : ℝ
  sumDiff : ℝ
  exceptional : ℝ
  l : ℝ
  logd : ℝ
  logf : ℝ
  C0 : ℝ
  V_le_step : V ≤ stepVExpr floorTerm sumB logp
  step_bound : stepVExpr floorTerm sumB logp ≤ stepVRHS lambda sumDiff logp exceptional
  box_bound : stepVRHS lambda sumDiff logp exceptional ≤ paperBox l logd logf C0

/-- Conditional volume upper from the Step-V dictionary. -/
theorem volume_upper_of_dictionary (D : StepVDictionary) :
    D.V ≤ paperBox D.l D.logd D.logf D.C0 :=
  volume_upper_of_stepV D.V (stepVExpr D.floorTerm D.sumB D.logp)
    D.lambda D.sumDiff D.logp D.exceptional D.l D.logd D.logf D.C0
    D.V_le_step D.step_bound D.box_bound

/-- Paper dictionary shape: `logdf = logd + logf` and the target coefficient
`(l+5)/4`.  These are the paper identifications needed on top of the object
identification; recorded as a Prop (not asserted). -/
def PaperDictionaryShape (l logd logf lambda sumDiff logp exceptional C0 : ℝ) : Prop :=
  paperBox l logd logf C0 = ((l + 5) / 4) * (logd + logf) + C0

theorem paperDictionaryShape_iff (l logd logf lambda sumDiff logp exceptional C0 : ℝ) :
    PaperDictionaryShape l logd logf lambda sumDiff logp exceptional C0 ↔
      paperBox l logd logf C0 = ((l + 5) / 4) * (logd + logf) + C0 := by
  unfold PaperDictionaryShape
  simp

def identRows : List (String × String × String) :=
  [ ("object identification", "V = (-floor(lambda-sumdiff-sumA)+sumB)logp", "GAP (no green carrier identification S1902/C3 vs lana hull(vcI))"),
    ("conditional assembly", "StepVDictionary => V <= paperBox", "PROVED (volume_upper_of_dictionary)"),
    ("paper logdf", "logdf = logd + logf = log d + log f", "DEF (paperBox)"),
    ("coefficient", "(l+5)/4, absolute C0", "DEF/PAPER"),
    ("paper dictionary shape", "paperBox = ((l+5)/4)(logd+logf)+C0", "DEF (PaperDictionaryShape)"),
    ("remaining", "identify lambda, sumDiff with logd/logf, and bound exceptional by absolute C0", "GAP") ]

theorem identRows_length : identRows.length = 6 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepVIdentificationActual.volume_upper_of_dictionary
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepVIdentificationActual.paperDictionaryShape_iff

end LeanFormal.IUT.XiFPaper.Mzk1StepVIdentificationActual

end