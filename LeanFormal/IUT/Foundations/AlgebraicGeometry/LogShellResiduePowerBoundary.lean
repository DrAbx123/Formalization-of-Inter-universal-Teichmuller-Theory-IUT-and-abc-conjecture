import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellVolumeConsumer
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexResidueFormula
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion

set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.LocalFields.LogShellResiduePowerBoundary

universe u

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume
open LeanFormal.IUT.NumberFieldFinitePlace

variable {K : Type u} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K] {p : ℕ} [Fact p.Prime]
  [NormedAlgebra ℚ_[p] K]

/-- Exact conditional boundary: the residue-power cardinal hypothesis for exponent
`a` holds if and only if the actual log-shell integer index is the `a`-th power
of the actual residue cardinal.  This is not an unconditional q^a claim. -/
theorem logShellResiduePowerCardHypothesis_iff_index_eq_pow {a : ℕ} :
    LogShellResiduePowerCardHypothesis (K := K) (p := p) a ↔
      logShellIntegerIndex (K := K) (p := p) =
        logShellResidueCard (K := K) ^ a := by
  constructor
  · exact logShellIntegerIndex_eq_residueCard_pow_of_powerCardHypothesis
  · intro h
    unfold LogShellResiduePowerCardHypothesis
    rw [logShellCongruenceQuotient_card_eq_torsion_mul_logShellIntegerIndex, h,
      Nat.mul_comm]

theorem logShellResiduePowerCardHypothesis_exists_iff_index_eq_pow :
    (∃ a : ℕ, LogShellResiduePowerCardHypothesis (K := K) (p := p) a) ↔
      ∃ a : ℕ, logShellIntegerIndex (K := K) (p := p) =
        logShellResidueCard (K := K) ^ a := by
  exact exists_congr (fun a => logShellResiduePowerCardHypothesis_iff_index_eq_pow)

/-- If the hypothesis holds for two exponents, they are equal: the residue
cardinal is at least two, so powers are injective in the exponent. -/
theorem logShellResiduePowerCardHypothesis_exponent_unique {a b : ℕ}
    (ha : LogShellResiduePowerCardHypothesis (K := K) (p := p) a)
    (hb : LogShellResiduePowerCardHypothesis (K := K) (p := p) b) :
    a = b := by
  have hqa : logShellIntegerIndex (K := K) (p := p) =
      logShellResidueCard (K := K) ^ a :=
    (logShellResiduePowerCardHypothesis_iff_index_eq_pow.mp ha)
  have hqb : logShellIntegerIndex (K := K) (p := p) =
      logShellResidueCard (K := K) ^ b :=
    (logShellResiduePowerCardHypothesis_iff_index_eq_pow.mp hb)
  have hpow : logShellResidueCard (K := K) ^ a =
      logShellResidueCard (K := K) ^ b := hqa.symm.trans hqb
  exact Nat.pow_right_injective
    (Nat.succ_le_of_lt (one_lt_logShellResidueCard (K := K) (p := p))) hpow

/-- Counterexample criterion: if the actual index is not a pure power of the
actual residue cardinal, no exponent satisfies the hypothesis. -/
theorem no_logShellResiduePowerCardHypothesis_of_not_pure_power
    (h : ¬ ∃ a : ℕ, logShellIntegerIndex (K := K) (p := p) =
      logShellResidueCard (K := K) ^ a) :
    ¬ ∃ a : ℕ, LogShellResiduePowerCardHypothesis (K := K) (p := p) a :=
  fun hh => h (logShellResiduePowerCardHypothesis_exists_iff_index_eq_pow.mp hh)

theorem not_logShellResiduePowerCardHypothesis_of_index_ne_pow {a : ℕ}
    (h : logShellIntegerIndex (K := K) (p := p) ≠
      logShellResidueCard (K := K) ^ a) :
    ¬ LogShellResiduePowerCardHypothesis (K := K) (p := p) a :=
  fun hh => h (logShellResiduePowerCardHypothesis_iff_index_eq_pow.mp hh)

theorem logShellResiduePowerCardHypothesis_zero_iff_index_eq_one :
    LogShellResiduePowerCardHypothesis (K := K) (p := p) 0 ↔
      logShellIntegerIndex (K := K) (p := p) = 1 := by
  rw [logShellResiduePowerCardHypothesis_iff_index_eq_pow, pow_zero]

/-- Actual consumers of the hypothesis, listed explicitly.  The hypothesis is
only ever consumed conditionally, never asserted unconditionally. -/
theorem logShellResiduePowerCardHypothesis_actual_consumers :
    (∀ a : ℕ, LogShellResiduePowerCardHypothesis (K := K) (p := p) a →
        logShellIntegerIndex (K := K) (p := p) =
          logShellResidueCard (K := K) ^ a) ∧
      (∀ a : ℕ, LogShellResiduePowerCardHypothesis (K := K) (p := p) a →
        (logShellVolumeConsumer (K := K) (p := p)).index =
          logShellResidueCard (K := K) ^ a) :=
  ⟨fun a h => logShellIntegerIndex_eq_residueCard_pow_of_powerCardHypothesis h,
    fun a h => logShellVolume_exact_residue_power h⟩

end LeanFormal.IUT.Foundations.LocalFields.LogShellResiduePowerBoundary
end