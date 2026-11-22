/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # Szpiro upper-bound direction: A/B correction assembly

Green A/B inputs (`IntegralLogShellSharpBounds`):
* `logShellPaperAExponent`, `logShellPaperBExponent`;
* `logShellPaperExponent_sum_mul_log_le_three_add_log`:
  `(A+B)*log p <= 3 + log e` (per prime);
* `stepVPaperCorrectionSum_le` (FinitePlaceStepVRealBound):
  the sum of A/B correction terms is bounded by `3 + log e` shape.

This file records the assembly step: a pointwise/total A/B bound gives an upper
bound for the correction sum, hence for the volume `V`; combined with the
Step-V upper volume bound it feeds `ssIneqExplicit_to_szpiro6`
(`Mzk1FinalBoundarySzpiroActual`).  The missing analytic input is the volume
upper bound `V <= (1/4) l logdf + C0`, not the A/B arithmetic. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1SzpiroUpperABActual

/-- Pointwise A/B bound sums to a total bound. -/
theorem AB_sum_le_of_pointwise {ι : Type*} [Fintype ι]
    (f g : ι → ℝ) (h : ∀ i, f i ≤ g i) :
    (∑ i, f i) ≤ ∑ i, g i :=
  Finset.sum_le_sum fun i _ => h i

/-- The assembled correction sum: `corr = Σ_i (A_i+B_i) * log p_i`. -/
def ABCorrectionSum {ι : Type*} [Fintype ι] (A B logp : ι → ℝ) : ℝ :=
  ∑ i, (A i + B i) * logp i

/-- If each prime satisfies `(A+B) log p <= 3 + log e`, the correction sum is
bounded by the sum of those bounds. -/
theorem ABCorrectionSum_le_sum_of_pointwise {ι : Type*} [Fintype ι]
    (A B logp e : ι → ℝ)
    (h : ∀ i, (A i + B i) * logp i ≤ 3 + Real.log (e i)) :
    ABCorrectionSum A B logp ≤ ∑ i, (3 + Real.log (e i)) := by
  unfold ABCorrectionSum
  exact Finset.sum_le_sum fun i _ => h i

/-- Volume upper bound from a correction bound. -/
def VolumeUpperBound (V corr C : ℝ) : Prop := V ≤ corr + C

/-- **Assembly**: `V <= corr + C` and `corr <= D` imply `V <= D + C`. -/
theorem volumeUpper_of_AB (V corr D C : ℝ)
    (hV : VolumeUpperBound V corr C) (hcorr : corr ≤ D) :
    V ≤ D + C := by
  unfold VolumeUpperBound at hV
  linarith

/-- Szpiro-6 shape (paper normalization). -/
def Szpiro6Shape (logq logdf C : ℝ) : Prop := logq ≤ 6 * logdf + C

/-- If the SSIneq explicit form and an upper volume bound `V <= (1/4)l logdf + C0`
hold, the forward Szpiro-6 shape follows; this is the interface consumed by
`Mzk1FinalBoundarySzpiroActual.ssIneqExplicit_to_szpiro6`.  The volume upper
bound is the analytic input, not proved here. -/
theorem szpiroUpper_interface
    (logq logdf V C0 c : ℝ) (hc : 0 < c)
    (hVup : V ≤ (6 * c) * logdf + C0)
    (hSS : c * logq ≤ V) :
    logq ≤ 6 * logdf + C0 / c := by
  have h1 : logq ≤ V / c := by
    rw [le_div_iff₀ hc]
    linarith [hSS]
  have h2 : V / c ≤ 6 * logdf + C0 / c := by
    rw [div_le_iff₀ hc]
    have hEq : (6 * logdf + C0 / c) * c = 6 * c * logdf + C0 := by
      field_simp [ne_of_gt hc]
    rw [hEq]
    exact hVup
  linarith

def szpiroRows : List (String × String × String) :=
  [ ("A/B exponents", "logShellPaperAExponent / logShellPaperBExponent", "GREEN (IntegralLogShellSharpBounds)"),
    ("per-prime A/B bound", "(A+B) log p <= 3 + log e", "GREEN (logShellPaperExponent_sum_mul_log_le_three_add_log)"),
    ("Step V sum", "stepVPaperCorrectionSum_le", "GREEN (FinitePlaceStepVRealBound)"),
    ("summation", "pointwise A/B => total correction bound", "PROVED (ABCorrectionSum_le_sum_of_pointwise)"),
    ("assembly", "V <= corr + C and corr <= D => V <= D + C", "PROVED (volumeUpper_of_AB)"),
    ("Szpiro interface", "c*logq <= V and V <= 6c*logdf + C0 => logq <= 6logdf + C0/c", "PROVED (szpiroUpper_interface); volume upper bound is the analytic input"),
    ("gap", "prove the volume upper bound V <= (1/4)l logdf + C0 from the actual hull (or from A/B + arch/torsion)", "GAP") ]

theorem szpiroRows_length : szpiroRows.length = 7 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1SzpiroUpperABActual.ABCorrectionSum_le_sum_of_pointwise
#print axioms LeanFormal.IUT.XiFPaper.Mzk1SzpiroUpperABActual.volumeUpper_of_AB
#print axioms LeanFormal.IUT.XiFPaper.Mzk1SzpiroUpperABActual.szpiroUpper_interface

end LeanFormal.IUT.XiFPaper.Mzk1SzpiroUpperABActual

end