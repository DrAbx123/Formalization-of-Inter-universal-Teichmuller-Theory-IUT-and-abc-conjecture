import tmp.sheaf.xif.paper.Mzk1IVThm110UnitLogNormBoundActual
import tmp.sheaf.xif.paper.NormalizedCompletionPadicBridgeActual
import tmp.sheaf.xif.paper.Mzk1IVThm110UnitLogNormHalfActual

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000
open scoped WithZero
open LeanFormal.IUT NumberField MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.NormalizedCompletionPadicBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitLogNormBoundActual

namespace LeanFormal.IUT.XiFPaper.NormalizedCompletionUnitLogActual

/-- For a rational normalized completion whose residual prime is at least 3,
every integral unit has `unitLog` of spectral norm at most one. -/
theorem unitLog_norm_le_one_normalizedCompletion
    (P : NumberField.FinitePlace ℚ)
    (h3 : 3 ≤ (completionRationalPrime P).val)
    (hcop : Nat.Coprime (completionRationalPrime P).val
      (integralUnitExponent (K := NormalizedCompletion P)))
    (u : (Integers (NormalizedCompletion P))ˣ) :
    ‖unitLog (K := NormalizedCompletion P) u‖ ≤ 1 := by
  letI : NormOneClass (NormalizedCompletion P) :=
    norm_one_class_normalizedCompletion P
  exact unitLog_norm_le_one_of_principal_bound
    (K := NormalizedCompletion P) (completionRationalPrime P).val
    (fun x hx => principal_unit_norm_le_third P h3 x hx) hcop u

/-- For p = 2 the principal-unit bound `≤ 1/2` and the tree's sharp
`log1p` half-ball estimate give the same `unitLog` norm bound.  The `ℚ_[2]`-algebra
instance is an explicit hypothesis because the completion's canonical scalar
instance is stated over its actual rational prime. -/
theorem unitLog_norm_le_one_normalizedCompletion_p2
    (P : NumberField.FinitePlace ℚ)
    [hinst : NormedAlgebra ℚ_[2] (NormalizedCompletion P)]
    (h2 : (completionRationalPrime P).val = 2)
    (hcop : Nat.Coprime 2 (integralUnitExponent (K := NormalizedCompletion P)))
    (u : (Integers (NormalizedCompletion P))ˣ) :
    ‖unitLog (K := NormalizedCompletion P) u‖ ≤ 1 := by
  exact LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitLogNormHalfActual.unitLog_norm_le_one_of_principal_bound_half
    (K := NormalizedCompletion P)
    (fun x hx => by
      have hle := principal_unit_norm_le_inv_prime P x hx
      have hp2 : ((completionRationalPrime P).val : ℝ) = 2 := by exact_mod_cast h2
      rw [hp2] at hle
      simpa [one_div] using hle)
    hcop u

end LeanFormal.IUT.XiFPaper.NormalizedCompletionUnitLogActual