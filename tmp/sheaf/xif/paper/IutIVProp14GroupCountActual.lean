/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexResidueFormula
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-! # IUT IV Prop 1.4: group-count reduction -/

noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
include localNormedAlgebra
/-- Exact two cardinal facts still needed for the Prop 1.4 local count:
the residue cardinal is `p^f`, and the closed congruence quotient has order
`(q-1) q^(e*s-1)`. -/
structure CongruenceQuotientCardinalityInput (e f : Nat) : Prop where
  one_le_e : 1 ≤ e
  residueCard_eq_prime_pow : logShellResidueCard (K := K) = p ^ f
  congruenceQuotient_card :
    Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
      logShellResidueCard (K := K) ^
          (e * logShellScaleExponentFactor (p := p) - 1) *
        (logShellResidueCard (K := K) - 1)
/-- The exact `LogShellQFECardinalityHypothesis` instance follows from the
two cardinal facts; no free `hqfe` is accepted by the consumer. -/
theorem logShellQFECardinalityHypothesis_actual
    {e f : Nat} (h : CongruenceQuotientCardinalityInput (K := K) (p := p) e f) :
    LogShellQFECardinalityHypothesis (K := K) (p := p) e f where
  one_le_ramificationExponent := h.one_le_e
  residueCard_eq_prime_pow_inertiaDegree := h.residueCard_eq_prime_pow
  congruenceQuotient_card_eq_residueUnits := h.congruenceQuotient_card
end LeanFormal.IUT.LocalFieldLogarithm
