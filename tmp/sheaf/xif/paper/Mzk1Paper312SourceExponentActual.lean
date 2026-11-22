/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Paper312ExponentInputActual
import tmp.sheaf.xif.paper.Mzk1ResiduePowerInstanceActual
import Mathlib.Tactic
/-! # Paper 3.12 exponent source: named `LogShellResiduePowerCardHypothesis a` -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Paper312SourceExponentActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1PerPlaceInequalityActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312ExponentInputActual
open LeanFormal.IUT.XiFPaper.Mzk1ResiduePowerInstanceActual
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
include localNormedAlgebra
/-- Source of the paper exponent `a_v`: the named hypothesis
`LogShellResiduePowerCardHypothesis a` says index = q^a. It is INDEPENDENT
of `eK*s - 1`; no construction from QFE exists in the tree. -/
theorem perPlace_of_powerCardHypothesis
    {f a Fdeg : Nat} {l logp logMu : ℝ}
    (hcard : LogShellResiduePowerCardHypothesis (K := K) (p := p) a)
    (hres : logShellResidueCard (K := K) = p ^ f)
    (hcoef : CoeffComparison (f : ℝ) (Fdeg : ℝ) l (a : ℝ))
    (hlogp_eq : logp = Real.log (p : ℝ))
    (hmu : 0 ≤ logMu) :
    (f : ℝ) / ((Fdeg : ℝ) * (2 * l)) * logp ≤
      (1 - 1 / (2 * l)) *
        Real.log (logShellIntegerIndex (K := K) (p := p) : ℝ) + logMu := by
  have hidx := logShellIntegerIndex_eq_residueCard_pow_of_powerCardHypothesis
    (K := K) (p := p) hcard
  have hlogidx := log_index_eq_mul_mul_log (K := K) (p := p)
    (index := logShellIntegerIndex (K := K) (p := p)) hres hidx
  have hlogp : 0 ≤ logp := by rw [hlogp_eq]; exact Real.log_nonneg (by exact_mod_cast (Fact.out : p.Prime).one_le)
  have h := perPlace_of_coeff_and_mu_nonneg hcoef hlogp hmu
  rw [hlogidx]
  simpa [hlogp_eq, mul_assoc, mul_comm, mul_left_comm] using h
end LeanFormal.IUT.XiFPaper.Mzk1Paper312SourceExponentActual
end