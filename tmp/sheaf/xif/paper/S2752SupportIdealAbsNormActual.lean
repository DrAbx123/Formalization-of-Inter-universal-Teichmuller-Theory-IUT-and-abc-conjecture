import tmp.sheaf.xif.paper.S2743LiesOverComapBridgeActual
import tmp.sheaf.xif.paper.S2751ExtendedAbsNormActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2752SupportIdealAbsNormActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2739FinsetSupportActual
open LeanFormal.IUT.XiFPaper.S2743LiesOverComapBridgeActual
open LeanFormal.IUT.XiFPaper.S2751ExtendedAbsNormActual

universe u
variable {K : Type u} [Field K] [NumberField K] [Algebra ℚ K]

/-- Every chosen support place has maximal-ideal absNorm at least the rational
prime, using the actual LiesOver bridge and S2751's unconditional rational
place absNorm. -/
theorem S2752_absNorm_supportPlace_ge_prime (x : ℚ) (i : SupportIndex x) :
    i.1 ≤ Ideal.absNorm ((supportPlace (K := K) x i).maximalIdeal.asIdeal) := by
  letI : Fact (Nat.Prime i.1) :=
    ⟨prime_of_mem_arithmeticPrimeSupport i.2⟩
  let P := (supportPlace (K := K) x i).maximalIdeal.asIdeal
  let q := (rationalFinitePlace i.1).maximalIdeal.asIdeal
  have hlies : P.LiesOver q := S2743_supportPlace_liesOver x i
  haveI : P.LiesOver q := hlies
  have hmain := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver
    (P := P) (p := q) (rationalFinitePlace i.1).maximalIdeal.isPrime
    (rationalFinitePlace i.1).maximalIdeal.ne_bot
  rw [S2751_absNorm_rationalFinitePlace i.1] at hmain
  let f := q.inertiaDeg' P
  have hf : 0 < f := Ideal.inertiaDeg'_pos (p := q) (P := P)
  have hle : i.1 ^ 1 ≤ i.1 ^ f :=
    Nat.pow_le_pow_right (Nat.Prime.pos Fact.out) hf
  rw [hmain]
  exact le_trans (by simp) hle

/-- The support-prime product is bounded by the support ideal absNorm. -/
theorem S2752_prod_support_le_supportIdeal_absNorm (x : ℚ) :
    (∏ i : SupportIndex x, i.1) ≤
      Ideal.absNorm (supportIdeal (K := K) x) := by
  rw [supportIdeal_absNorm]
  exact Finset.prod_le_prod (fun i _ => Nat.zero_le _)
    (fun i _ => S2752_absNorm_supportPlace_ge_prime x i)

#check S2752_absNorm_supportPlace_ge_prime
#check S2752_prod_support_le_supportIdeal_absNorm
#print axioms S2752_prod_support_le_supportIdeal_absNorm

end LeanFormal.IUT.XiFPaper.S2752SupportIdealAbsNormActual
end
