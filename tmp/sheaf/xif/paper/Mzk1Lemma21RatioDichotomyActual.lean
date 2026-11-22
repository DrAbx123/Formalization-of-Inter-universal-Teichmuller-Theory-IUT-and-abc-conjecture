import tmp.sheaf.xif.paper.Mzk1Lemma21RatioOddActual
import Mathlib.Tactic

/-! # Mzk1Lemma21RatioDichotomyActual — [Mzk1] Lemma 2.1(d), n odd: alpha>1 dichotomy (arithmetic part)

STEP 0 prior-art: corpus Lemma 2.1 lines 97-105 (the two cases f(alpha)>=f0 and
f(alpha)<=f0 in the n odd proof); Mzk1Lemma21RatioOddActual (f0=-f(r)=|f(r)|,
0<f0, f0<=1, alpha in {0,1} case); Mzk1Lemma21RatioActual (estimate (e) chain).
No Mathlib shortcut needed for the arithmetic; reused Elementary real inequalities.

PAPER (n odd, alpha>1):
* if f(alpha) >= f0:  (f(beta)+f0)/(f(alpha)+f0) >= f(beta)/(2 f(alpha))
  >= (1/2)(beta/alpha)^2 >= beta/alpha >= C;
* if f(alpha) <= f0:  (f(beta)+f0)/(f(alpha)+f0) >= f(beta)/(2 f0) >= 2 f(beta)
  >= beta >= C   [using 0 < f0 <= 1/4, beta >= C >= 2].

THIS FILE PROVES the two ARITHMETIC comparison lemmas (finite real form), with the
geometric inputs (f(beta) >= (beta/alpha)^2 f(alpha) resp. 0<f0<=1/4) as explicit
hypotheses.  Those geometric inputs are the remaining obligations. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioDichotomyActual

/-- Case f(alpha) >= f0: denominator is at most 2 f(alpha), numerator at least f(beta),
so a multiplicative bound 2 C f(alpha) <= f(beta) suffices. -/
theorem ratio_ge_of_f0_le_falpha {fβ fα f0 C : ℝ}
    (hαpos : 0 < fα + f0) (hf0nonneg : 0 ≤ f0) (hf0le : f0 ≤ fα)
    (hC0 : 0 ≤ C) (hC2 : 2 * C * fα ≤ fβ) :
    C ≤ (fβ + f0) / (fα + f0) := by
  rw [le_div_iff₀ hαpos]
  have hden : fα + f0 ≤ 2 * fα := by linarith
  have hnum : fβ ≤ fβ + f0 := by linarith
  have h1 : C * (fα + f0) ≤ C * (2 * fα) :=
    mul_le_mul_of_nonneg_left hden hC0
  have h2 : C * (2 * fα) = 2 * C * fα := by ring
  linarith

/-- Case f(alpha) <= f0: denominator is at most 2 f0, numerator at least f(beta),
and 0 < f0 <= 1/4 gives 2 f(beta) f0 <= f(beta) + f0. -/
theorem ratio_ge_of_falpha_le_f0 {fβ fα f0 C : ℝ}
    (hαpos : 0 < fα + f0) (hf0pos : 0 < f0) (hf0quarter : f0 ≤ 1 / 4)
    (hαle : fα ≤ f0) (hβnonneg : 0 ≤ fβ) (hC0 : 0 ≤ C) (hCβ : C ≤ fβ) :
    C ≤ (fβ + f0) / (fα + f0) := by
  rw [le_div_iff₀ hαpos]
  have hden : fα + f0 ≤ 2 * f0 := by linarith
  have h1 : C * (fα + f0) ≤ C * (2 * f0) :=
    mul_le_mul_of_nonneg_left hden hC0
  have h2 : C * (2 * f0) ≤ 2 * fβ * f0 := by nlinarith [hCβ, hf0pos]
  have h3 : 2 * fβ * f0 ≤ fβ + f0 := by nlinarith [hf0quarter, hf0pos, hβnonneg]
  linarith

/-- Combined odd-case dichotomy: given the two geometric inputs in whichever case
applies, the (d) ratio bound holds. -/
theorem ratio_ge_dichotomy {fβ fα f0 C : ℝ}
    (hαpos : 0 < fα + f0) (hf0pos : 0 < f0) (hf0nonneg : 0 ≤ f0)
    (hC0 : 0 ≤ C) (hβnonneg : 0 ≤ fβ) :
    (f0 ≤ fα → 2 * C * fα ≤ fβ → C ≤ (fβ + f0) / (fα + f0)) ∧
    (fα ≤ f0 → f0 ≤ 1 / 4 → C ≤ fβ → C ≤ (fβ + f0) / (fα + f0)) := by
  constructor
  · intro hle hC2
    exact ratio_ge_of_f0_le_falpha hαpos hf0nonneg hle hC0 hC2
  · intro hle hquarter hCβ
    exact ratio_ge_of_falpha_le_f0 hαpos hf0pos hquarter hle hβnonneg hC0 hCβ

#check ratio_ge_of_f0_le_falpha
#check ratio_ge_of_falpha_le_f0
#check ratio_ge_dichotomy

end LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioDichotomyActual
end
