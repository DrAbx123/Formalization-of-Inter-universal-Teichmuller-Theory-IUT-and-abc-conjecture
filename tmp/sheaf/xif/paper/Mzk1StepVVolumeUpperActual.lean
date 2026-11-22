/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A816 hull: Step-V -> paper box volume upper

Target shape (paper, absolute constant `C0`):

  `V <= ((l + 5)/4) * logdf + C0`,   `logdf = log d + log f`.

Green `FinitePlaceStepVRealBound.stepVPaperLogVolumeBound` gives

  `stepV <= (-lambda + sum differentOrder + 1) * log p
            + sum_{exceptional} (3 + log ramIdx)`

where `stepV = (-floor(lambda - sum diff - sum A) + sum B) * log p`.
This file assembles the conditional box theorem; the object identification
`V = stepV` (or `V <= stepV`), the paper dictionary of `lambda/diff` with
`logdf`, and the absolute bound for the exceptional sum are the remaining
inputs (not fabricated). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeUpperActual

/-- Paper `logdf = log d + log f`. -/
def logdf (logd logf : ℝ) : ℝ := logd + logf

/-- Paper box `((l+5)/4)*logdf + C0` with absolute `C0`. -/
def paperBox (l logd logf C0 : ℝ) : ℝ := ((l + 5) / 4) * logdf logd logf + C0

theorem paperBox_eq (l logd logf C0 : ℝ) :
    paperBox l logd logf C0 = ((l + 5) / 4) * (logd + logf) + C0 := rfl

/-- Step-V log-volume expression `(-floor + sumB) * logp`. -/
def stepVExpr (floorTerm sumB logp : ℝ) : ℝ := (-floorTerm + sumB) * logp

/-- Green Step-V RHS `(-lambda + sumDiff + 1) logp + exceptional`. -/
def stepVRHS (lambda sumDiff logp exceptional : ℝ) : ℝ :=
  (-lambda + sumDiff + 1) * logp + exceptional

/-- **Conditional Step-V upper**: `V <= stepV`, `stepV <= stepVRHS`, and
`stepVRHS <= paperBox` imply the paper box. -/
theorem volume_upper_of_stepV
    (V stepV lambda sumDiff logp exceptional l logd logf C0 : ℝ)
    (hV : V ≤ stepV)
    (hstep : stepV ≤ stepVRHS lambda sumDiff logp exceptional)
    (hbox : stepVRHS lambda sumDiff logp exceptional ≤ paperBox l logd logf C0) :
    V ≤ paperBox l logd logf C0 := by
  linarith

/-- Direct object-identification form: `V = stepVExpr`. -/
theorem volume_upper_of_identification
    (V floorTerm sumB lambda sumDiff logp exceptional l logd logf C0 : ℝ)
    (hident : V = stepVExpr floorTerm sumB logp)
    (hstep : stepVExpr floorTerm sumB logp ≤ stepVRHS lambda sumDiff logp exceptional)
    (hbox : stepVRHS lambda sumDiff logp exceptional ≤ paperBox l logd logf C0) :
    V ≤ paperBox l logd logf C0 := by
  rw [hident]
  linarith

/-- Constant decomposition: the exceptional sum is absorbed into `C0` when it is
bounded by the absolute constant. -/
theorem volume_upper_of_exceptional_abs
    (V stepV RHSmain exceptional l logd logf C0 Cexc : ℝ)
    (hV : V ≤ stepV)
    (hstep : stepV ≤ RHSmain + exceptional)
    (hexc : exceptional ≤ Cexc)
    (hbox : RHSmain + Cexc ≤ paperBox l logd logf C0) :
    V ≤ paperBox l logd logf C0 := by
  linarith

/-- The coefficient `(l+5)/4` is the procession-average box constant: recorded
as an explicit identity so the target shape is not confused with `(1/4)l` or
`l/24` coefficients. -/
theorem box_coefficient_shape (l : ℝ) :
    ((l + 5) / 4 : ℝ) = (l + 5) / 4 := rfl

def stepVRows : List (String × String × String) :=
  [ ("target shape", "V <= ((l+5)/4)*logdf + C0, logdf=logd+logf, C0 absolute", "DEF (paperBox)"),
    ("stepV expression", "stepV = (-floor(lambda-sumdiff-sumA)+sumB)*logp", "DEF (stepVExpr)"),
    ("green Step-V bound", "stepV <= (-lambda+sumdiff+1)logp + sum_except(3+log e)", "GREEN (FinitePlaceStepVRealBound.stepVPaperLogVolumeBound; cited)"),
    ("conditional assembly", "V<=stepV, stepV<=stepVRHS, stepVRHS<=box => V<=box", "PROVED (volume_upper_of_stepV)"),
    ("identification form", "V=stepVExpr => box", "PROVED (volume_upper_of_identification)"),
    ("exceptional absorption", "exceptional<=Cexc and main+Cexc<=box => V<=box", "PROVED (volume_upper_of_exceptional_abs)"),
    ("coefficient", "(l+5)/4 from procession; not (1/4)l and not l/24", "DEF/PAPER"),
    ("gap 1", "object identification V = (-floor+sumB)logp", "GAP"),
    ("gap 2", "paper dictionary lambda/diff <-> logd, logf and absolute bound for exceptional sum", "GAP"),
    ("gap 3", "exceptional sum bounded independent of D (bad-place count/boundedness)", "GAP") ]

theorem stepVRows_length : stepVRows.length = 10 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeUpperActual.volume_upper_of_stepV
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeUpperActual.volume_upper_of_identification
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeUpperActual.volume_upper_of_exceptional_abs

end LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeUpperActual

end