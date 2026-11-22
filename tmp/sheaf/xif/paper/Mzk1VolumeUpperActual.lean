/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A810 hull: volume upper bound `V <= (1/4)l logdf + C0`

Green `FinitePlaceStepVRealBound.stepVPaperLogVolumeBound` bounds

  `(-floor(lambda - sum differentOrder - sum A) + sum B) * log p`
  `<= (-lambda + sum differentOrder + 1) * log p + sum_{exceptional}(3 + log ramIdx)`.

This is a bound on the **Step-V log-volume expression**, not directly on our
paper-normalized hull log-volume `V` (the `S1902/scaled θ` volume).  The exact
bridge needed is the identification

  `V = (-floor(...) + sum B) * log p`

(plus the `lambda/differentOrder` data and the global sum over bad places).
With that identification the green bound gives
`V <= (-lambda + sum differentOrder + 1)log p + exceptional correction`; to
obtain `V <= (1/4)l logdf + C0` one still needs the paper identification of
`lambda`, `differentOrder`, `logdf` and the exceptional correction constant.

The arithmetic assembly below is proved; the object identification is the gap. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1VolumeUpperActual

/-- Abstract Step-V log-volume expression. -/
def StepVLogVolume (floorTerm sumB logp : ℝ) : ℝ := (-floorTerm + sumB) * logp

/-- The green `stepVPaperLogVolumeBound` has the shape
`StepVLogVolume floor sumB logp <= (-lambda + sumDiff + 1) * logp + exceptional`.
It is recorded as an explicit hypothesis (the green theorem itself is cited). -/
def StepVBound (stepV RHS : ℝ) : Prop := stepV ≤ RHS

/-- Volume upper bound interface. -/
def VolumeUpperBound (V L : ℝ) : Prop := V ≤ L

/-- **Conditional volume upper**: if `V = stepV`, the green Step-V bound
`stepV <= RHS`, and `RHS <= (1/4)l logdf + C0`, then `V <= (1/4)l logdf + C0`. -/
theorem volumeUpper_of_stepV_identification
    (V stepV RHS l logdf C0 : ℝ)
    (hident : V = stepV) (hstep : StepVBound stepV RHS)
    (hpaper : RHS ≤ (1 / 4) * l * logdf + C0) :
    V ≤ (1 / 4) * l * logdf + C0 := by
  unfold StepVBound at hstep
  rw [hident]
  linarith

/-- Arithmetic version with the Step-V RHS coefficients: if the green bound gives
`stepV <= (-lambda + sumDiff + 1)logp + exceptional`, and this RHS is controlled
by `(1/4)l logdf + C0`, the volume upper follows. -/
theorem volumeUpper_of_stepV_rhs
    (V stepV lambda sumDiff logp exceptional l logdf C0 : ℝ)
    (hident : V = stepV)
    (hstep : stepV ≤ (-lambda + sumDiff + 1) * logp + exceptional)
    (hpaper : (-lambda + sumDiff + 1) * logp + exceptional ≤
      (1 / 4) * l * logdf + C0) :
    V ≤ (1 / 4) * l * logdf + C0 := by
  rw [hident]
  linarith

/-- The global sum over bad places: if each place satisfies the per-place volume
upper and the sum of constants is `C0`, the global upper follows (finite index). -/
theorem volumeUpper_global_of_perPlace {ι : Type*} [Fintype ι]
    (V : ℝ) (perPlace : ι → ℝ) (C0 : ℝ)
    (hV : V ≤ ∑ i, perPlace i) (hconst : ∑ i, perPlace i ≤ C0) :
    V ≤ C0 := by
  linarith

def volumeRows : List (String × String × String) :=
  [ ("green Step-V bound", "stepVPaperLogVolumeBound: (-floor+sumB)logp <= (-lambda+sumDiff+1)logp + exceptional", "GREEN (FinitePlaceStepVRealBound)"),
    ("object check", "the green bound is on the Step-V log-volume expression, NOT directly on our V = scaled θ hull log-volume", "MISMATCH"),
    ("needed identification", "V = (-floor+sumB)logp (with lambda, differentOrder data)", "GAP"),
    ("conditional assembly", "V=stepV, stepV<=RHS, RHS<=(1/4)l logdf+C0 => V upper", "PROVED (volumeUpper_of_stepV_identification)"),
    ("Step-V RHS form", "same with (-lambda+sumDiff+1)logp+exceptional", "PROVED (volumeUpper_of_stepV_rhs)"),
    ("global gluing", "per-place upper + sum constants => global upper", "PROVED (volumeUpper_global_of_perPlace)"),
    ("remaining paper data", "identify lambda, differentOrder, exceptional correction with logdf and constants", "GAP") ]

theorem volumeRows_length : volumeRows.length = 7 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1VolumeUpperActual.volumeUpper_of_stepV_identification
#print axioms LeanFormal.IUT.XiFPaper.Mzk1VolumeUpperActual.volumeUpper_of_stepV_rhs
#print axioms LeanFormal.IUT.XiFPaper.Mzk1VolumeUpperActual.volumeUpper_global_of_perPlace

end LeanFormal.IUT.XiFPaper.Mzk1VolumeUpperActual

end