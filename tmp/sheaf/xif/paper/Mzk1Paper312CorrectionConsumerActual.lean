/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Paper312ExponentInputActual
import tmp.sheaf.xif.paper.Mzk1IutIVCongruenceCardActual
import Mathlib.Tactic
/-! # Paper 3.12 per-place consumer for the correction hypothesis -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Paper312CorrectionConsumerActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1PerPlaceInequalityActual
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
include localNormedAlgebra
/-- Per-place bound from the correction hypothesis `index=q^a*c`, `c≥1`. -/
theorem perPlace_of_correction
    {f a : Nat} {Fdeg l logp logMu : ℝ} (c : Nat)
    (hcard : LogShellResiduePowerCardCorrectionHypothesis (K := K) (p := p) a c)
    (hres : logShellResidueCard (K := K) = p ^ f)
    (hcoef : CoeffComparison (f : ℝ) (Fdeg : ℝ) l (a : ℝ))
    (hlogp_eq : logp = Real.log (p : ℝ))
    (hmu : 0 ≤ logMu) (hl : 1 ≤ 2 * l) (hc : 1 ≤ c) :
    (f : ℝ) / ((Fdeg : ℝ) * (2 * l)) * logp ≤
      (1 - 1 / (2 * l)) *
        Real.log (logShellIntegerIndex (K := K) (p := p) : ℝ) + logMu := by
  have hidx := logShellIntegerIndex_eq_residueCard_pow_mul_correction_of_card
    (K := K) (p := p) hcard
  have hqpos : 0 < logShellResidueCard (K := K) :=
    logShellResidueCard_pos (K := K) (p := p)
  have hcpos : 0 < (c : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hc)
  have hqR : (0 : ℝ) < (logShellResidueCard (K := K) : ℝ) := by
    exact_mod_cast hqpos
  have hlogidx : Real.log (logShellIntegerIndex (K := K) (p := p) : ℝ) =
      (a : ℝ) * Real.log (logShellResidueCard (K := K) : ℝ) + Real.log (c : ℝ) := by
    calc Real.log (logShellIntegerIndex (K := K) (p := p) : ℝ)
        = Real.log ((logShellResidueCard (K := K) : ℝ) ^ a * (c : ℝ)) := by
            rw [hidx, Nat.cast_mul, Nat.cast_pow]
      _ = Real.log ((logShellResidueCard (K := K) : ℝ) ^ a) + Real.log (c : ℝ) :=
            Real.log_mul
              (pow_ne_zero a (ne_of_gt hqR))
              (ne_of_gt hcpos)
      _ = (a : ℝ) * Real.log (logShellResidueCard (K := K) : ℝ) + Real.log (c : ℝ) := by
            rw [Real.log_pow]
  have hlogq : Real.log (logShellResidueCard (K := K) : ℝ) =
      (f : ℝ) * Real.log (p : ℝ) := by
    rw [hres, Nat.cast_pow, Real.log_pow]
  have hlogp : 0 ≤ logp := by
    rw [hlogp_eq]
    exact Real.log_nonneg (by exact_mod_cast (Fact.out : p.Prime).one_le)
  have hcoefnonneg : 0 ≤ 1 - 1 / (2 * l) := by
    rw [sub_nonneg, div_le_one (by positivity : (0 : ℝ) < 2 * l)]
    exact hl
  have hlogc : 0 ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast hc)
  have h := perPlace_of_coeff_and_mu_nonneg hcoef hlogp hmu
  have hcomm : (1 - 1 / (2 * l)) * (f : ℝ) * (a : ℝ) * logp =
      (1 - 1 / (2 * l)) * ((a : ℝ) * (f : ℝ) * Real.log (p : ℝ)) := by
    rw [hlogp_eq]
    ring
  rw [hcomm] at h
  rw [hlogp_eq] at h
  rw [hlogp_eq]
  calc
    (f : ℝ) / ((Fdeg : ℝ) * (2 * l)) * Real.log (p : ℝ)
        ≤ (1 - 1 / (2 * l)) *
            ((a : ℝ) * (f : ℝ) * Real.log (p : ℝ)) + logMu := h
    _ ≤ (1 - 1 / (2 * l)) *
          ((a : ℝ) * (f : ℝ) * Real.log (p : ℝ) + Real.log (c : ℝ)) + logMu := by
          have hprod : 0 ≤ (1 - 1 / (2 * l)) * Real.log (c : ℝ) :=
            mul_nonneg hcoefnonneg hlogc
          nlinarith [hprod]
    _ = (1 - 1 / (2 * l)) *
          Real.log (logShellIntegerIndex (K := K) (p := p) : ℝ) + logMu := by
          rw [hlogidx, hlogq]
          ring
end LeanFormal.IUT.XiFPaper.Mzk1Paper312CorrectionConsumerActual
end