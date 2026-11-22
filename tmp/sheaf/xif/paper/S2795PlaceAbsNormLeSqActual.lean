import tmp.sheaf.xif.paper.S2743LiesOverComapBridgeActual
import tmp.sheaf.xif.paper.S2690TwoPlaceBadQActual
import tmp.sheaf.xif.paper.ArithmeticLineBundleActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Int

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2739FinsetSupportActual
open LeanFormal.IUT.XiFPaper.S2743LiesOverComapBridgeActual
open LeanFormal.IUT.XiFPaper.S2690TwoPlaceBadQActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2795PlaceAbsNormLeSqActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- For the chosen support place over `x`, its maximal-ideal absolute norm is at most
the square of the underlying rational prime.  K = Q(i) has finrank 2 over Q. -/
theorem S2795_place_absNorm_le_sq (x : ℚ) (i : SupportIndex x) :
    Ideal.absNorm ((supportPlace (K := GaussianField) x i).maximalIdeal.asIdeal) ≤
      i.1 ^ 2 := by
  haveI : Fact (Nat.Prime i.1) :=
    ⟨prime_of_mem_arithmeticPrimeSupport i.2⟩
  let P : Ideal (NumberField.RingOfIntegers GaussianField) :=
    (supportPlace (K := GaussianField) x i).maximalIdeal.asIdeal
  let q : Ideal (NumberField.RingOfIntegers ℚ) :=
    (rationalFinitePlace i.1).maximalIdeal.asIdeal
  let p : Ideal ℤ := q.under ℤ
  have hlies : P.LiesOver q :=
    S2743_supportPlace_liesOver (K := GaussianField) x i
  haveI : P.IsPrime :=
    (supportPlace (K := GaussianField) x i).maximalIdeal.isPrime
  haveI : P.LiesOver q := hlies
  have hPunder : Ideal.under ℤ P = p := by
    rw [← Ideal.under_under (A := ℤ) (B := NumberField.RingOfIntegers ℚ) P]
    rw [S2743_supportPlace_under]
  haveI hPp : P.LiesOver p := ⟨hPunder.symm⟩
  have hp_prime : p.IsPrime :=
    Ideal.comap_isPrime (algebraMap ℤ (NumberField.RingOfIntegers ℚ)) q
  have hq0 : q ≠ ⊥ := by
    simpa [q] using (rationalFinitePlace i.1).maximalIdeal.ne_bot
  have hp0 : p ≠ ⊥ :=
    Ideal.IsIntegral.comap_ne_bot (R := ℤ) (I := q) hq0
  have hp_max : p.IsMaximal := hp_prime.isMaximal hp0
  haveI : p.IsMaximal := hp_max
  have hf : p.inertiaDeg' P ≤ Module.finrank ℚ GaussianField :=
    Ideal.inertiaDeg_le_finrank (R := ℤ)
      (S := NumberField.RingOfIntegers GaussianField)
      (K := ℚ) (L := GaussianField) (p := p) P hp0
  have hfr : Module.finrank ℚ GaussianField = 2 := gaussianField_finrank
  have hf2 : p.inertiaDeg' P ≤ 2 := by
    simpa [hfr] using hf
  have habs : Ideal.absNorm P = Ideal.absNorm p ^ p.inertiaDeg' P :=
    Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver (S := ℤ)
      (R := NumberField.RingOfIntegers GaussianField)
      P p hp_prime hp0
  have hpabs : Ideal.absNorm p = i.1 := by
    have hqabs : Ideal.absNorm q = i.1 := by
      simpa [q] using absNorm_rationalFinitePlace i.1
    have hdiv : Ideal.absNorm p ∣ i.1 := by
      have h := Int.absNorm_under_dvd_absNorm (S := NumberField.RingOfIntegers ℚ) q
      rwa [hqabs] at h
    have hpabsprime : Nat.Prime (Ideal.absNorm p) :=
      Nat.absNorm_under_prime (R := NumberField.RingOfIntegers ℚ) q
    exact (((Fact.out : Nat.Prime i.1).dvd_iff_eq hpabsprime.ne_one).mp hdiv).symm
  rw [habs, hpabs]
  exact Nat.pow_le_pow_right (Nat.Prime.pos Fact.out) hf2

#check S2795_place_absNorm_le_sq
#print axioms S2795_place_absNorm_le_sq

end LeanFormal.IUT.XiFPaper.S2795PlaceAbsNormLeSqActual
end