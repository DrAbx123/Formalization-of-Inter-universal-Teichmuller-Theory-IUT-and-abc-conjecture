import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIntegerQuotient
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexArithmetic

open scoped Multiplicative

set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.LocalFields.LogShellQuotientConsumer

universe u

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm

variable {K : Type u} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K] {p : ℕ} [Fact p.Prime]
  [NormedAlgebra ℚ_[p] K]

/-- Actual log-shell integer quotient consumer over a local base: a finite
quotient of the integral log-shell by its valuation-integer subgroup, with the
actual full-unit log map as quotient map. -/
structure LogShellIntegerQuotientConsumer where
  quotient : Type u
  [quotientAddCommMonoid : AddCommMonoid quotient]
  finite : Finite quotient
  quotientMap : (Integers K)ˣ →* Multiplicative quotient
  quotientMap_surjective : Function.Surjective quotientMap
  index : ℕ
  index_eq_card : index = Nat.card quotient
  index_pos : 0 < index

/-- The actual consumer, built from the production integral log-shell quotient. -/
noncomputable def logShellIntegerQuotientConsumer :
    LogShellIntegerQuotientConsumer (K := K) where
  quotient := LogShellIntegerQuotient (K := K) (p := p)
  quotientAddCommMonoid := inferInstance
  finite := finite_logShellIntegerQuotient (K := K) (p := p)
  quotientMap := unitLogIntegerQuotientHom (K := K) (p := p)
  quotientMap_surjective := unitLogIntegerQuotientHom_surjective (K := K) (p := p)
  index := logShellIntegerIndex (K := K) (p := p)
  index_eq_card := rfl
  index_pos := logShellIntegerIndex_pos (K := K) (p := p)

theorem logShellIntegerQuotientConsumer_quotientMap_surjective :
    Function.Surjective (logShellIntegerQuotientConsumer (K := K) (p := p)).quotientMap :=
  (logShellIntegerQuotientConsumer (K := K) (p := p)).quotientMap_surjective

theorem logShellIntegerQuotientConsumer_finite :
    Finite (logShellIntegerQuotientConsumer (K := K) (p := p)).quotient :=
  (logShellIntegerQuotientConsumer (K := K) (p := p)).finite

theorem logShellIntegerQuotientConsumer_index_pos :
    0 < (logShellIntegerQuotientConsumer (K := K) (p := p)).index :=
  (logShellIntegerQuotientConsumer (K := K) (p := p)).index_pos

end LeanFormal.IUT.Foundations.LocalFields.LogShellQuotientConsumer
end