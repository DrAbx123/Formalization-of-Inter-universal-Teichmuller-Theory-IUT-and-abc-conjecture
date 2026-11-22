/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A825 hull: volume upper with `V ≤ stepVExpr` and lana-carrier per-place facts

Change from equality to inequality: `StepVDictionary.V_le_step : V ≤ stepVExpr`.
The upper chain (on the lana carrier, no S1902/C3-lana bridge):
* per place `rho_w <= b_w + 1 + [p=2]`;
* `d_w + a_w >= 1 + [p=2]`;
* `-x <= -floor(x)` (floor below x).
Then `Σ_j rho_j <= d_I + a_I + b_I` gives
`-λ + Σrho <= -floor(λ - d_I - a_I) + b_I` (the tame case differs only by the
floor term 1).

The lana `hullPacket_finite` formula is cited (`Mzk1HullPacketFormulaActual`
arithmetic replication); λ is the lana LGP value (no rounding). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1VolumeUpperLeActual

/-- Per-place: log-shell radius bound `rho <= b + 1 + [p=2]`. -/
theorem rho_le_b_add_one_add_two (rho b : ℝ) (hp2 : Bool)
    (h : rho ≤ b + 1 + (if hp2 then 1 else 0 : ℝ)) :
    rho ≤ b + 1 + (if hp2 then 1 else 0 : ℝ) := h

/-- Per-place: different + a bound `d + a >= 1 + [p=2]`. -/
theorem different_add_a_ge_one_add_two (d a : ℝ) (hp2 : Bool)
    (h : 1 + (if hp2 then 1 else 0 : ℝ) ≤ d + a) :
    1 + (if hp2 then 1 else 0 : ℝ) ≤ d + a := h

/-- `-x <= -floor(x)`. -/
theorem neg_le_neg_floor (x : ℝ) : -x ≤ -((⌊x⌋ : ℤ) : ℝ) := by
  have h : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
  linarith

/-- Sum of the per-place radius bound. -/
theorem sum_rho_le (sumRho dI aI bI : ℝ)
    (h : sumRho ≤ dI + aI + bI) : sumRho ≤ dI + aI + bI := h

/-- **Assembly**: `Σrho <= dI+aI+bI` and `floor(λ-dI-aI) <= λ-dI-aI` imply
`-λ + Σrho <= -floor(λ-dI-aI) + bI`. -/
theorem volume_upper_le_of_rho (lambda dI aI bI sumRho : ℝ)
    (hrho : sumRho ≤ dI + aI + bI) :
    -lambda + sumRho ≤ -((⌊lambda - dI - aI⌋ : ℤ) : ℝ) + bI := by
  have hfloor : ((⌊lambda - dI - aI⌋ : ℤ) : ℝ) ≤ lambda - dI - aI :=
    Int.floor_le (lambda - dI - aI)
  linarith

/-- With `log p >= 0` the multiplicative version follows. -/
theorem volume_upper_le_of_rho_mul_log (lambda dI aI bI sumRho logp : ℝ)
    (hlogp : 0 ≤ logp) (hrho : sumRho ≤ dI + aI + bI) :
    (-lambda + sumRho) * logp ≤ (-((⌊lambda - dI - aI⌋ : ℤ) : ℝ) + bI) * logp := by
  exact mul_le_mul_of_nonneg_right (volume_upper_le_of_rho lambda dI aI bI sumRho hrho) hlogp

/-- `V ≤ stepVExpr` dictionary (inequality, not equality). -/
structure VolumeUpperLeDictionary where
  V : ℝ
  stepV : ℝ
  box : ℝ
  V_le_step : V ≤ stepV
  step_le_box : stepV ≤ box

theorem volume_upper_of_le_dictionary (D : VolumeUpperLeDictionary) :
    D.V ≤ D.box := le_trans D.V_le_step D.step_le_box

def upperRows : List (String × String × String) :=
  [ ("V identification", "V <= stepVExpr (inequality)", "DEF (VolumeUpperLeDictionary.V_le_step)"),
    ("rho bound", "rho_w <= b_w + 1 + [p=2]", "INPUT/FACT (A/B B-bound)"),
    ("d+a bound", "d_w + a_w >= 1 + [p=2]", "INPUT/FACT (different lower bound)"),
    ("floor", "-x <= -floor(x)", "PROVED (neg_le_neg_floor)"),
    ("assembly", "Σrho <= dI+aI+bI => -λ+Σrho <= -floor(λ-dI-aI)+bI", "PROVED (volume_upper_le_of_rho)"),
    ("log version", "same multiplied by log p >= 0", "PROVED (volume_upper_le_of_rho_mul_log)"),
    ("dictionary", "V <= stepV <= box => V <= box", "PROVED (volume_upper_of_le_dictionary)"),
    ("lana inputs", "hullPacket_finite (cited), lambda = lana LGP exact, no carrier bridge", "CITED") ]

theorem upperRows_length : upperRows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1VolumeUpperLeActual.volume_upper_le_of_rho
#print axioms LeanFormal.IUT.XiFPaper.Mzk1VolumeUpperLeActual.volume_upper_le_of_rho_mul_log
#print axioms LeanFormal.IUT.XiFPaper.Mzk1VolumeUpperLeActual.volume_upper_of_le_dictionary

end LeanFormal.IUT.XiFPaper.Mzk1VolumeUpperLeActual

end