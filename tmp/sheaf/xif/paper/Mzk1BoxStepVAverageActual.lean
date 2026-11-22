import LeanFormal.IUT.IUTIV.Estimates.StepVDistinguishedSlotAverage
import Mathlib.Tactic
/-! StepV distinguished-slot average, wired for the actual packet readout.

This is a readout-level wrapper: once every tuple's actual signed readout is bounded by
`collectionChoiceBound` at a fixed distinguished slot, the weighted average obeys the paper's
`collectionBound`.  No new analytic input is added here. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1BoxStepVAverageActual
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.IUTIV.StepVDistinguishedSlotAverage
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
universe u
/-- Actual StepV weighted-average step: it suffices to bound the signed readout at one
distinguished slot. -/
theorem stepV_weightedAverage_le_of_distinguished
    {E : Type u} [Fintype E] [Nonempty E]
    (lam : E -> Real) (weights_pos : ∀ e, 0 < lam e)
    (l logp iotaL : Real) (l_ne_zero : l ≠ 0)
    (j : Nat) (d oq : E -> Real) (slot : Fin (j + 1))
    (V : (Fin (j + 1) -> E) -> Real)
    (bound : ∀ et, V et ≤ collectionChoiceBound l logp iotaL j d oq et slot) :
    (∑ et : Fin (j + 1) -> E, V et * ∏ i, lam (et i)) /
      (∑ et : Fin (j + 1) -> E, ∏ i, lam (et i)) ≤
    collectionBound l ((∑ e, d e * logp * lam e) / ∑ e, lam e)
      ((∑ e, oq e * logp * lam e) / ∑ e, lam e) logp iotaL j :=
  weightedAverage_le_of_distinguishedBound lam weights_pos l logp iotaL l_ne_zero
    j d oq slot V bound
/-- Paper-level procession average from distinguished-slot bounds. -/
theorem stepV_procession_le_of_distinguished
    {E : Type u} [Fintype E] [Nonempty E]
    (n : Nat) (n_ge_two : 2 ≤ n)
    (lam : E -> Real) (weights_pos : ∀ e, 0 < lam e)
    (logp iotaL : Real) (d oq : E -> Real)
    (different_nonneg : 0 ≤ (∑ e, d e * logp * lam e) / ∑ e, lam e)
    (logp_nonneg : 0 ≤ logp) (iotaL_nonneg : 0 ≤ iotaL)
    (slot : (j : Nat) -> Fin (j + 1))
    (V : (j : Nat) -> (Fin (j + 1) -> E) -> Real)
    (bound : ∀ j ∈ Finset.Icc 1 n, ∀ et,
      V j et ≤ collectionChoiceBound (2 * (n : Real) + 1) logp iotaL j d oq et (slot j)) :
    1 / (n : Real) * ∑ j ∈ Finset.Icc 1 n,
      (∑ et : Fin (j + 1) -> E, V j et * ∏ i, lam (et i)) /
        (∑ et : Fin (j + 1) -> E, ∏ i, lam (et i)) ≤
    (2 * (n : Real) + 1 + 1) / 4 *
      ((1 + 4 / (2 * (n : Real) + 1)) * ((∑ e, d e * logp * lam e) / (∑ e, lam e)) -
        ((∑ e, oq e * logp * lam e) / (∑ e, lam e)) / 6 +
        (4 / (2 * (n : Real) + 1)) * logp + (20 / 3) * iotaL) :=
  processionNormalized_le_of_distinguishedBounds n n_ge_two lam weights_pos logp iotaL
    d oq different_nonneg logp_nonneg iotaL_nonneg slot V bound
end LeanFormal.IUT.XiFPaper.Mzk1BoxStepVAverageActual
end
