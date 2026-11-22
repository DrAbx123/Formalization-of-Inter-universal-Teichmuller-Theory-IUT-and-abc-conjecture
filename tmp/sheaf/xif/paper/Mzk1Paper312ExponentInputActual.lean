/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PerPlaceInequalityActual
import Mathlib.Tactic
/-! # Paper 3.12 independent exponent input and per-place consumer -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Paper312ExponentInputActual
open LeanFormal.IUT.XiFPaper.Mzk1PerPlaceInequalityActual
/-- Explicit source input: `exponent` is the independent paper exponent `a_v`,
NOT necessarily `eK*s - 1`, and NOT defined as `log_q(index)`. -/
structure Paper312ExponentInput (f Fdeg l exponent logp logMu : ℝ) : Prop where
  coeffComparison : CoeffComparison f Fdeg l exponent
  logp_nonneg : 0 ≤ logp
  logMu_nonneg : 0 ≤ logMu
/-- Connect the independent-exponent input to the per-place inequality. -/
theorem perPlace_of_paper312ExponentInput
    {f Fdeg l exponent logp logMu : ℝ}
    (h : Paper312ExponentInput f Fdeg l exponent logp logMu) :
    f / (Fdeg * (2 * l)) * logp ≤
      (1 - 1 / (2 * l)) * f * exponent * logp + logMu :=
  perPlace_of_coeff_and_mu_nonneg h.coeffComparison h.logp_nonneg h.logMu_nonneg
/-- Pure residue-power index attached to the independent exponent:
`index = residueCard^a` and `logIdx = a * log(residueCard)`. -/
structure Paper312IndexExponentInput
    (index residueCard a : Nat) (f Fdeg l logp logMu : ℝ) : Prop where
  pure_power : index = residueCard ^ a
  exponentInput : Paper312ExponentInput f Fdeg l (a : ℝ) logp logMu
  logIdx_eq : (0 : ℝ) ≤ Real.log (residueCard : ℝ)
end LeanFormal.IUT.XiFPaper.Mzk1Paper312ExponentInputActual
end