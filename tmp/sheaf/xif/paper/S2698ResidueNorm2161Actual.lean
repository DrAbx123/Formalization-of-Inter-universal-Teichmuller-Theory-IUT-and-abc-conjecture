import tmp.sheaf.xif.paper.S2696GaussianPlace2161Actual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import Mathlib.RingTheory.Ideal.Int

noncomputable section
set_option maxRecDepth 100000
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2696GaussianPlace2161Actual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

namespace LeanFormal.IUT.XiFPaper.S2698ResidueNorm2161Actual

local instance s2698GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2698Fact2161 : Fact (Nat.Prime 2161) := ⟨by decide⟩

theorem S2698PrimeOver_liesOver_span :
    S2696PrimeOver.ideal.LiesOver (Ideal.span {(2161 : ℤ)}) := by
  simpa [S2696IntegerPrimeIdeal] using S2696PrimeOver.liesOver

theorem S2698_absNorm :
    Ideal.absNorm S2696PrimeOver.ideal =
      2161 ^ (Ideal.span {(2161 : ℤ)}).inertiaDeg' S2696PrimeOver.ideal := by
  haveI : S2696PrimeOver.ideal.LiesOver (Ideal.span {(2161 : ℤ)}) :=
    S2698PrimeOver_liesOver_span
  exact Ideal.absNorm_eq_pow_inertiaDeg' S2696PrimeOver.ideal (p := 2161) s2698Fact2161.out

theorem S2698_residueNormBase_ge :
    (2161 : ℝ) ≤ residueNormBase S2696GaussianPlace := by
  unfold residueNormBase
  rw [S2696GaussianPlace_maximalIdeal]
  haveI : S2696PrimeOver.ideal.LiesOver (Ideal.span {(2161 : ℤ)}) :=
    S2698PrimeOver_liesOver_span
  rw [S2698_absNorm]
  haveI hmax : (Ideal.span {(2161 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 2161
  have hf : 0 < (Ideal.span {(2161 : ℤ)}).inertiaDeg' S2696PrimeOver.ideal :=
    Ideal.inertiaDeg'_pos (Ideal.span {(2161 : ℤ)}) S2696PrimeOver.ideal
  have hf1 : 1 ≤ (Ideal.span {(2161 : ℤ)}).inertiaDeg' S2696PrimeOver.ideal :=
    Nat.succ_le_of_lt hf
  have hpow : (2161 : ℝ) ^ 1 ≤
      (2161 : ℝ) ^ (Ideal.span {(2161 : ℤ)}).inertiaDeg' S2696PrimeOver.ideal :=
    pow_le_pow_right₀ (by norm_num) hf1
  simpa using hpow

#check S2698_residueNormBase_ge
#print axioms S2698_residueNormBase_ge

end LeanFormal.IUT.XiFPaper.S2698ResidueNorm2161Actual
end
