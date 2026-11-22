/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds
import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellResiduePowerBoundary
import tmp.sheaf.xif.paper.Mzk1Paper312ConditionsActual
import Mathlib.Tactic

/-! # A789: residue-card / index instance for condition (1) -/

/- GREEN: `logShellResidueCard_eq_prime_pow` (SharpBounds:1014) gives UNCONDITIONALLY
`∃ f, 1 ≤ f ∧ logShellResidueCard = p^f`; `logShellResiduePowerCardHypothesis_iff_index_eq_pow`
(ResiduePowerBoundary:27) gives `LogShellResiduePowerCardHypothesis a ↔ index = rc^a`.
So condition (1)'s residue side is instantiated unconditionally; only the exponent `a` is a
named (non-computable here) cardinal input. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ResiduePowerInstanceActual

open LeanFormal.IUT.Foundations.LocalFields
open LeanFormal.IUT.Foundations.LocalFields.LogShellResiduePowerBoundary
open LeanFormal.IUT.LocalFieldLogarithm

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K]
variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] K]

/-- Condition (1), residue side (UNCONDITIONAL): residueCard = p^f with f >= 1. -/
theorem residueCard_eq_prime_pow_instance :
    ∃ f : ℕ, 1 ≤ f ∧ logShellResidueCard (K := K) = p ^ f :=
  logShellResidueCard_eq_prime_pow (K := K) (p := p)

/-- Condition (1), index side (equivalence with the named cardinal hypothesis). -/
theorem index_eq_pow_iff_hypothesis (a : ℕ) :
    LeanFormal.IUT.XiFPaper.Mzk1Paper312ConditionsActual.ResiduePowerCondition
        (logShellIntegerIndex (K := K) (p := p)) (logShellResidueCard (K := K)) a ↔
      LogShellResiduePowerCardHypothesis (K := K) (p := p) a :=
  (logShellResiduePowerCardHypothesis_iff_index_eq_pow (K := K) (p := p) (a := a)).symm

/-- Under the residue-power condition: `log index = a * log residueCard`. -/
theorem log_index_eq_mul_log_residueCard {a : ℕ}
    (h : logShellIntegerIndex (K := K) (p := p) = logShellResidueCard (K := K) ^ a) :
    Real.log (logShellIntegerIndex (K := K) (p := p) : ℝ) =
      (a : ℝ) * Real.log (logShellResidueCard (K := K) : ℝ) := by
  rw [h]
  rw [Nat.cast_pow]
  rw [Real.log_pow]

/-- Explicit power form: if `residueCard = p^f` and `index = residueCard^a`, then
`log index = a*f*log p`. -/
theorem log_index_eq_mul_mul_log {p f a : ℕ} {index : ℕ}
    (hres : logShellResidueCard (K := K) = p ^ f)
    (hidx : index = logShellResidueCard (K := K) ^ a) :
    Real.log (index : ℝ) = (a : ℝ) * ((f : ℝ) * Real.log (p : ℝ)) := by
  rw [hidx, hres, ← pow_mul]
  rw [Nat.cast_pow]
  rw [Real.log_pow]
  push_cast
  ring

end LeanFormal.IUT.XiFPaper.Mzk1ResiduePowerInstanceActual
