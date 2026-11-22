import tmp.sheaf.xif.paper.Mzk1CThetaComparisonActual
import LeanFormal.IUT.Foundations.Theta.OddThetaNormalization

/-!
# P5-A: analytic oddTheta normalization vs the q_v^(j^2) root value

This file states the one normalization identity that currently connects the
analytic oddTheta special values to the paper root-value exponent:

  (oddTheta q (i * r^j) / oddTheta q i)^(-1) = r^(j^2).

It is a direct corollary of OddThetaNormalization.oddThetaFraction_eval.

It is NOT a construction of the paperRootThetaUnit bridge: the analytic
oddTheta lives in a normed field L, while paperRootThetaUnit lives in an
algebraic closure of a p-adic completion. No map between them, no Kummer
class, and no line-bundle section is constructed here; see
coord/ROUTE3-CTHETA.md P5-A for the exact missing objects.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P5ThetaBridgeActual

open LeanFormal.IUT.Foundations.Theta

variable {L : Type*} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- The reciprocal normalized oddTheta value has exactly the q_v^(j^2)
exponent form used by paperRootThetaUnit. -/
theorem oddThetaFraction_inv_eq_pow
    (q r i : L) (hr : r ^ 2 = q) (hr0 : r ≠ 0) (hi : i ^ 2 = -1)
    (hq : ‖q‖ < 1) (hTheta : oddTheta q i ≠ 0) (j : Int) :
    (oddTheta q (i * r ^ j) / oddTheta q i)⁻¹ = r ^ (j ^ 2) := by
  rw [oddThetaFraction_eval q r i hr hr0 hi hq hTheta j]
  rw [zpow_neg]
  simp

#print axioms oddThetaFraction_inv_eq_pow

end LeanFormal.IUT.XiFPaper.Mzk1P5ThetaBridgeActual
