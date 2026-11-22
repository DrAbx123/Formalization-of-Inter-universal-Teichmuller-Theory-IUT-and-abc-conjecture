import tmp.sheaf.xif.paper.S2782Curve37a1Actual
import tmp.sheaf.xif.paper.S2763ResidueCharacteristicUnitActual
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import tmp.sheaf.xif.paper.S2786E37PrimeIdealsActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2782Curve37a1Actual
open LeanFormal.IUT.XiFPaper.S2763ResidueCharacteristicUnitActual
open LeanFormal.IUT.XiFPaper.S2786E37PrimeIdealsActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

local instance s2794GaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := by
  apply Fact.mk
  apply X_pow_sub_C_irreducible_of_prime (p := 2) Nat.prime_two
  intro b hb
  have hnonneg : 0 <= b ^ 2 := sq_nonneg b
  rw [hb] at hnonneg
  exact (not_le_of_gt (neg_lt_zero.mpr zero_lt_one)) hnonneg

namespace LeanFormal.IUT.XiFPaper.S2794Multiplicative37Actual

variable (P : NumberField.FinitePlace GaussianField)

abbrev K (P : NumberField.FinitePlace GaussianField) : Type :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletion GaussianField P.maximalIdeal

abbrev R (P : NumberField.FinitePlace GaussianField) : Type :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers GaussianField P.maximalIdeal

def localIntegralModel37Qi : WeierstrassCurve (R P) where
  a₁ := 0
  a₂ := 0
  a₃ := 1
  a₄ := -1
  a₆ := 0

def localCurve37Qi : WeierstrassCurve (K P) :=
  (localIntegralModel37Qi P).map (algebraMap (R P) (K P))

theorem localCurve37Qi_isIntegral : (localCurve37Qi P).IsIntegral (R P) := by
  apply WeierstrassCurve.isIntegral_of_exists_lift
  · exact ⟨0, by simp [localCurve37Qi, localIntegralModel37Qi]⟩
  · exact ⟨0, by simp [localCurve37Qi, localIntegralModel37Qi]⟩
  · exact ⟨1, by simp [localCurve37Qi, localIntegralModel37Qi]⟩
  · exact ⟨-1, by simp [localCurve37Qi, localIntegralModel37Qi]⟩
  · exact ⟨0, by simp [localCurve37Qi, localIntegralModel37Qi]⟩

theorem localIntegralModel37Qi_delta :
    (localIntegralModel37Qi P).Δ = (37 : R P) := by
  norm_num [localIntegralModel37Qi, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem localIntegralModel37Qi_c4 :
    (localIntegralModel37Qi P).c₄ = (48 : R P) := by
  norm_num [localIntegralModel37Qi, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]

theorem localCurve37Qi_delta :
    (localCurve37Qi P).Δ = algebraMap (R P) (K P) (37 : R P) := by
  rw [localCurve37Qi, WeierstrassCurve.map_Δ, localIntegralModel37Qi_delta]

theorem localCurve37Qi_c4 :
    (localCurve37Qi P).c₄ = algebraMap (R P) (K P) (48 : R P) := by
  rw [localCurve37Qi, WeierstrassCurve.map_c₄, localIntegralModel37Qi_c4]

theorem thirtyseven_not_unit (h37 : residueCharacteristic P = 37) :
    ¬ IsUnit ((37 : Nat) : R P) := by
  intro hunit
  have hnot : ¬ residueCharacteristic P ∣ (37 : Nat) :=
    (isUnit_natCast_adicCompletionIntegers_iff_not_dvd (K := GaussianField) P 37).mp hunit
  exact hnot (by simpa [h37])

theorem fortyeight_unit (h37 : residueCharacteristic P = 37) :
    IsUnit ((48 : Nat) : R P) := by
  rw [isUnit_natCast_adicCompletionIntegers_iff_not_dvd]
  intro hdvd
  have h : residueCharacteristic P ∣ (48 : Nat) := hdvd
  rw [h37] at h
  norm_num at h


theorem not_dvd_thirtyseven_of_ne
    (h37 : residueCharacteristic P ≠ 37) :
    ¬ residueCharacteristic P ∣ (37 : Nat) := by
  intro hd
  have hp : Nat.Prime (residueCharacteristic P) := residueCharacteristic_prime P
  have h37prime : Nat.Prime (37 : Nat) := by decide
  have heq : (37 : Nat) = residueCharacteristic P :=
    (h37prime.dvd_iff_eq hp.ne_one).mp hd
  exact h37 heq.symm

theorem localCurve37Qi_delta_isUnit
    (h37 : residueCharacteristic P ≠ 37) :
    IsUnit (localCurve37Qi P).Δ := by
  rw [localCurve37Qi_delta]
  exact IsUnit.map (algebraMap (R P) (K P))
    ((isUnit_natCast_adicCompletionIntegers_iff_not_dvd (K := GaussianField) P 37).mpr
      (not_dvd_thirtyseven_of_ne P h37))

theorem localCurve37Qi_hasGoodReduction
    (h37 : residueCharacteristic P ≠ 37) :
    (localCurve37Qi P).HasGoodReduction (R P) := by
  letI : (localCurve37Qi P).IsIntegral (R P) := localCurve37Qi_isIntegral P
  have hval : (IsDiscreteValuationRing.maximalIdeal (R P)).valuation (K P)
      (localCurve37Qi P).Δ = 1 := by
    rw [localCurve37Qi_delta]
    exact (IsDiscreteValuationRing.maximalIdeal (R P)).valuation_eq_one_iff_notMem
      (K := K P) |>.mpr
        (IsLocalRing.notMem_maximalIdeal.mpr
          ((isUnit_natCast_adicCompletionIntegers_iff_not_dvd (K := GaussianField) P 37).mpr
            (not_dvd_thirtyseven_of_ne P h37)))
  letI : (localCurve37Qi P).IsMinimal (R P) :=
    isMinimal_of_isIntegral_valuation_Δ_eq_one (R P) (localCurve37Qi P) hval
  exact { goodReduction := hval }

theorem localCurve37Qi_hasGoodReductionOnMinimalModel
    (h37 : residueCharacteristic P ≠ 37) :
    HasGoodReductionOnMinimalModel (R P) (localCurve37Qi P) :=
  ⟨1, by simpa using localCurve37Qi_hasGoodReduction P h37⟩

theorem localCurve37Qi_delta_valuation_lt_one
    (h37 : residueCharacteristic P = 37) :
    (IsDiscreteValuationRing.maximalIdeal (R P)).valuation (K P)
      (localCurve37Qi P).Δ < 1 := by
  have hmem : (37 : R P) ∈ IsLocalRing.maximalIdeal (R P) :=
    (IsLocalRing.mem_maximalIdeal (37 : R P)).mpr
      ((mem_nonunits_iff).mpr (thirtyseven_not_unit P h37))
  rw [localCurve37Qi_delta]
  exact ((IsDiscreteValuationRing.maximalIdeal (R P)).valuation_lt_one_iff_mem
    (K := K P) (37 : R P)).mpr hmem

theorem localCurve37Qi_c4_valuation_eq_one
    (h37 : residueCharacteristic P = 37) :
    (IsDiscreteValuationRing.maximalIdeal (R P)).valuation (K P)
      (localCurve37Qi P).c₄ = 1 := by
  have hnot : (48 : R P) ∉ IsLocalRing.maximalIdeal (R P) :=
    IsLocalRing.notMem_maximalIdeal.mpr (fortyeight_unit P h37)
  rw [localCurve37Qi_c4]
  exact ((IsDiscreteValuationRing.maximalIdeal (R P)).valuation_eq_one_iff_notMem
    (K := K P)).mpr hnot

theorem localCurve37Qi_isMinimal
    (h37 : residueCharacteristic P = 37) :
    (localCurve37Qi P).IsMinimal (R P) := by
  letI : (localCurve37Qi P).IsIntegral (R P) := localCurve37Qi_isIntegral P
  exact isMinimal_of_isIntegral_valuation_c₄_eq_one (R P) (localCurve37Qi P)
    (localCurve37Qi_c4_valuation_eq_one P h37)

theorem localCurve37Qi_hasMultiplicativeReduction
    (h37 : residueCharacteristic P = 37) :
    (localCurve37Qi P).HasMultiplicativeReduction (R P) := by
  letI : (localCurve37Qi P).IsIntegral (R P) := localCurve37Qi_isIntegral P
  letI : (localCurve37Qi P).IsMinimal (R P) := localCurve37Qi_isMinimal P h37
  exact { badReduction := localCurve37Qi_delta_valuation_lt_one P h37,
          multiplicativeReduction := localCurve37Qi_c4_valuation_eq_one P h37 }

theorem plus37_hasMultiplicativeReduction :
    (localCurve37Qi gaussianField37PlusPlace).HasMultiplicativeReduction
      (R gaussianField37PlusPlace) :=
  localCurve37Qi_hasMultiplicativeReduction gaussianField37PlusPlace
    gaussianField37PlusPlace_residueCharacteristic

theorem minus37_hasMultiplicativeReduction :
    (localCurve37Qi gaussianField37MinusPlace).HasMultiplicativeReduction
      (R gaussianField37MinusPlace) :=
  localCurve37Qi_hasMultiplicativeReduction gaussianField37MinusPlace
    gaussianField37MinusPlace_residueCharacteristic

#check localCurve37Qi_hasMultiplicativeReduction
#check plus37_hasMultiplicativeReduction
#check minus37_hasMultiplicativeReduction
#print axioms plus37_hasMultiplicativeReduction
#print axioms minus37_hasMultiplicativeReduction

end LeanFormal.IUT.XiFPaper.S2794Multiplicative37Actual
end
