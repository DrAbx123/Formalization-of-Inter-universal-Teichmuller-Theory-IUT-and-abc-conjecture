import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegreeGlobal
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.GoingUp

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2696GaussianPlace2161Actual

local instance s2696GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

def S2696IntegerPrimeIdeal : Ideal ℤ :=
  Ideal.span {(2161 : ℤ)}

theorem S2696IntegerPrimeIdeal_isPrime :
    S2696IntegerPrimeIdeal.IsPrime := by
  rw [S2696IntegerPrimeIdeal, Ideal.span_singleton_prime (by norm_num : (2161 : ℤ) ≠ 0)]
  decide

instance S2696IntegerPrimeIdeal_isMaximal :
    S2696IntegerPrimeIdeal.IsMaximal :=
  S2696IntegerPrimeIdeal_isPrime.isMaximal (by
    rw [S2696IntegerPrimeIdeal]
    exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (2161 : ℤ) ≠ 0))

/-- An actual prime ideal of the Gaussian integers over (2161). -/
structure S2696PrimeOverData where
  ideal : Ideal (NumberField.RingOfIntegers GaussianField)
  isMaximal : ideal.IsMaximal
  liesOver : ideal.LiesOver S2696IntegerPrimeIdeal

noncomputable def S2696PrimeOver : S2696PrimeOverData := by
  let h := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := NumberField.RingOfIntegers GaussianField)
    (R := ℤ) S2696IntegerPrimeIdeal
  exact ⟨Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2⟩

noncomputable def S2696GaussianPlace : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk
    { asIdeal := S2696PrimeOver.ideal
      isPrime := S2696PrimeOver.isMaximal.isPrime
      ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField
        S2696PrimeOver.isMaximal (NumberField.RingOfIntegers.not_isField GaussianField) }

theorem S2696GaussianPlace_maximalIdeal :
    S2696GaussianPlace.maximalIdeal.asIdeal = S2696PrimeOver.ideal :=
  congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
    (NumberField.FinitePlace.maximalIdeal_mk _)

theorem S2696GaussianPlace_liesOverInteger :
    S2696IntegerPrimeIdeal =
      S2696GaussianPlace.maximalIdeal.asIdeal.comap
        (algebraMap ℤ (NumberField.RingOfIntegers GaussianField)) := by
  rw [S2696GaussianPlace_maximalIdeal]
  exact S2696PrimeOver.liesOver.over

#print axioms S2696GaussianPlace_liesOverInteger

end LeanFormal.IUT.XiFPaper.S2696GaussianPlace2161Actual
end
