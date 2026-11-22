import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm

/-!
# ShehddIntegralUnitLogConsumerActual — integral unit logarithm consumer

Consumer chain over IntegralUnitLogarithm with the prime `p` as an explicit parameter:
unitLog is a monoid hom to the additive local field (multiplicative/power/unit laws),
agrees with log1p on principal units, and is independent of the chosen uniform exponent.
No sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddIntegralUnitLogConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K] [IsUltrametricDist K]

/-- **PROVED consumer:** the actual unit logarithm is a monoid hom to the additive local
field: multiplicative law, power law and unit law. -/
theorem unitLog_hom_consumer (p : Nat) [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    [ProperSpace K] (u v : (Integers K)ˣ) (n : Nat) :
    unitLog (u * v) = unitLog u + unitLog v ∧
      unitLog (u ^ n) = (n : K) * unitLog u ∧
        unitLog (1 : (Integers K)ˣ) = 0 :=
  ⟨unitLog_mul u v, unitLog_pow u n, unitLog_one⟩

/-- **PROVED consumer:** on principal units, the constructed log agrees with the
analytic series log1p (u - 1). -/
theorem unitLog_principal_consumer (p : Nat) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] K] [ProperSpace K] (u : (Integers K)ˣ)
    (hu : u ∈ principalUnits) :
    unitLog u = log1p ((u.val : K) - 1) :=
  unitLog_eq_log1p u hu

/-- **PROVED consumer:** any positive exponents landing in principal units give the same
extended log value (finite-quotient independence). -/
theorem unitLog_exponent_independence_consumer (p : Nat) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] K] [ProperSpace K] (u : (Integers K)ˣ)
    {n m : Nat} (hn : n ≠ 0) (hm : m ≠ 0)
    (hun : u ^ n ∈ principalUnits) (hum : u ^ m ∈ principalUnits) :
    unitLogWithExponent n u = unitLogWithExponent m u :=
  unitLogWithExponent_independent u hn hm hun hum

end LeanFormal.IUT.XiFPaper.ShehddIntegralUnitLogConsumerActual
end
