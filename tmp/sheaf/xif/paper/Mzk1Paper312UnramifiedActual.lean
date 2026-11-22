/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Paper312CorrectionConsumerActual
import tmp.sheaf.xif.paper.Mzk1PerPlaceBoundHullActual
import Mathlib.Tactic
/-! # Unramified A=0 obstruction and correction-to-diff composition -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Paper312UnramifiedActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1PerPlaceInequalityActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312CorrectionConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1PerPlaceBoundHullActual
open scoped NNReal NormedField
/-- Unramified odd-p obstruction: with `logMu = 0`, `a=0`, `c=1`, the
per-place bound fails already for `p=3, f=1, Fdeg=1, l=1`. -/
theorem unramified_odd_obstruction :
    ¬ (Real.log 3 / (2 * 1) ≤ (0 : ℝ) + (1 - 1 / (2 * 1)) * 0) := by
  have h : 0 < Real.log 3 := Real.log_pos (by norm_num)
  intro hc
  nlinarith
/-- Compose the correction consumer with the `diff` reduction. -/
theorem perPlace_diff_of_correction
    {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K]
    {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
    {fn a c : Nat} {Fdeg l logp logMu logIdx diff : ℝ}
    (hcard : LogShellResiduePowerCardCorrectionHypothesis (K := K) (p := p) a c)
    (hres : logShellResidueCard (K := K) = p ^ fn)
    (hcoef : CoeffComparison (fn : ℝ) Fdeg l (a : ℝ))
    (hlogp_eq : logp = Real.log (p : ℝ))
    (hmu0 : 0 ≤ logMu) (hl : 1 ≤ 2 * l) (hc : 1 ≤ c)
    (hlogIdx : logIdx = Real.log (logShellIntegerIndex (K := K) (p := p) : ℝ))
    (hdiff : diff = logMu - (1 / (2 * l)) * logIdx) :
    (fn : ℝ) / (Fdeg * (2 * l)) * logp ≤ logIdx + diff := by
  have h := perPlace_of_correction (K := K) (p := p) c hcard hres hcoef
    hlogp_eq hmu0 hl hc
  rw [← hlogIdx] at h
  exact perPlace_inequality_of_mu_lower_diff
    ((fn : ℝ) / (Fdeg * (2 * l)) * logp) logIdx logMu diff logMu l le_rfl hdiff
    (by simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using h)
end LeanFormal.IUT.XiFPaper.Mzk1Paper312UnramifiedActual
end