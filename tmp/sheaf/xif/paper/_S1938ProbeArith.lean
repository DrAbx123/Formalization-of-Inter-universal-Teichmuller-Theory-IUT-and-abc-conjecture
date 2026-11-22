import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteInitialThetaFiniteArithmetic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1938Probe

open LeanFormal.IUT
open scoped BigOperators

variable {l : PrimeGeFive}

theorem s1938_abs_label_le (j : SignedLabel l.value) :
    |((j.1 : ℤ) : ℝ)| ≤ (lStar l.value : ℝ) := by
  have h1 : ((j.1 : ℤ) : ℝ) ≤ (lStar l.value : ℝ) := by
    exact_mod_cast j.2.2
  have h2 : -((lStar l.value : ℝ)) ≤ ((j.1 : ℤ) : ℝ) := by
    have h := j.2.1
    have h' : ((-(lStar l.value : ℤ) : ℤ) : ℝ) ≤ ((j.1 : ℤ) : ℝ) := by exact_mod_cast h
    simpa using h'
  exact abs_le.mpr ⟨h2, h1⟩

theorem s1938_label_sq_le (j : SignedLabel l.value) :
    ((j.1 : ℤ) : ℝ) ^ 2 ≤ (lStar l.value : ℝ) ^ 2 := by
  have h := s1938_abs_label_le (l := l) j
  calc ((j.1 : ℤ) : ℝ) ^ 2 = |((j.1 : ℤ) : ℝ)| ^ 2 := (sq_abs _).symm
    _ ≤ (lStar l.value : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2

theorem s1938_sum_sq_le :
    (∑ j : SignedLabel l.value, ((j.1 : ℤ) : ℝ) ^ 2) ≤ (l.value : ℝ) ^ 3 := by
  have hstep : (∑ j : SignedLabel l.value, ((j.1 : ℤ) : ℝ) ^ 2) ≤
      ∑ _j : SignedLabel l.value, (lStar l.value : ℝ) ^ 2 :=
    Finset.sum_le_sum (fun j _ => s1938_label_sq_le (l := l) j)
  have hconst : (∑ _j : SignedLabel l.value, (lStar l.value : ℝ) ^ 2) =
      (l.value : ℝ) * (lStar l.value : ℝ) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, SignedLabel.card_signedLabel l]
  have hstar0 : (0 : ℝ) ≤ (lStar l.value : ℝ) := Nat.cast_nonneg _
  have hstarle : (lStar l.value : ℝ) ≤ (l.value : ℝ) := by
    have h : lStar l.value ≤ l.value := (concreteLabel_star_lt l).le
    exact_mod_cast h
  have hsq : (lStar l.value : ℝ) ^ 2 ≤ (l.value : ℝ) ^ 2 :=
    pow_le_pow_left₀ hstar0 hstarle 2
  have hl0 : (0 : ℝ) ≤ (l.value : ℝ) := Nat.cast_nonneg _
  calc (∑ j : SignedLabel l.value, ((j.1 : ℤ) : ℝ) ^ 2)
      ≤ (l.value : ℝ) * (lStar l.value : ℝ) ^ 2 := hstep.trans (le_of_eq hconst)
    _ ≤ (l.value : ℝ) * (l.value : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq hl0
    _ = (l.value : ℝ) ^ 3 := by ring

end LeanFormal.IUT.XiFPaper.S1938Probe
