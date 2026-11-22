import tmp.sheaf.xif.paper.S2739FinsetSupportActual
import tmp.sheaf.xif.paper.S2690TwoPlaceBadQActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2738PrimeOverFamilyActual
open LeanFormal.IUT.XiFPaper.S2739FinsetSupportActual
open LeanFormal.IUT.XiFPaper.S2690TwoPlaceBadQActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2743SupportIdealAbsNormLowerActual

variable {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]

/-- Every chosen support place has maximal-ideal absNorm at least the
underlying rational prime. -/
theorem S2743_absNorm_supportPlace_ge_prime (x : ℚ) (i : SupportIndex x) :
    i.1 ≤ Ideal.absNorm ((supportPlace (K := K) x i).maximalIdeal.asIdeal) := by
  haveI : Fact (Nat.Prime i.1) := ⟨prime_of_mem_arithmeticPrimeSupport i.2⟩
  let P := (supportPlace (K := K) x i).maximalIdeal.asIdeal
  let q := (rationalFinitePlace i.1).maximalIdeal.asIdeal
  have hcomap : comap (k := ℚ) (supportPlace (K := K) x i) = rationalFinitePlace i.1 := by
    simpa [supportRationalPlace] using supportPlace_comap (K := K) x i
  have hcomapMax := NumberFieldFinitePlace.comap_maximalIdeal
    (k := ℚ) (K := K) (supportPlace (K := K) x i)
  rw [hcomap] at hcomapMax
  have hlies : P.LiesOver q := (Ideal.liesOver_iff _ _).mpr hcomapMax
  letI : P.LiesOver q := hlies
  have hmain := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver
    (P := P) (p := q) (rationalFinitePlace i.1).maximalIdeal.isPrime
    (rationalFinitePlace i.1).maximalIdeal.ne_bot
  rw [absNorm_rationalFinitePlace] at hmain
  let f := q.inertiaDeg' P
  have hf : 0 < f := Ideal.inertiaDeg'_pos (p := q) (P := P)
  have hle : i.1 ^ 1 ≤ i.1 ^ f := by
    exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime i.1)) hf
  rw [hmain]
  change i.1 ≤ i.1 ^ (q.inertiaDeg' P)
  simpa [f] using hle

/-- The product of the support primes is bounded by the absNorm of the chosen
support ideal. -/
theorem S2743_prod_support_le_supportIdeal_absNorm (x : ℚ) :
    (∏ i : SupportIndex x, i.1) ≤
      Ideal.absNorm (supportIdeal (K := K) x) := by
  rw [supportIdeal_absNorm]
  exact Finset.prod_le_prod (fun i _ => Nat.zero_le _)
    (fun i _ => S2743_absNorm_supportPlace_ge_prime x i)

#check S2743_prod_support_le_supportIdeal_absNorm
#print axioms S2743_prod_support_le_supportIdeal_absNorm

end LeanFormal.IUT.XiFPaper.S2743SupportIdealAbsNormLowerActual
end
