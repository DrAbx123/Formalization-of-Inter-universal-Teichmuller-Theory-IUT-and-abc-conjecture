import tmp.sheaf.xif.paper.Mzk1BoxActualR2Actual
import LeanFormal.IUT.IUTIV.Estimates.StepVDistinguishedSlotAverage
import Mathlib.Tactic
/-!
# R2 per-row IV:1585: distinguished-slot choice averages to `collectionBound`

Separate file so `Mzk1BoxActualR2Actual` (DONE 20:27:15/20:44:05) is not touched.
Reuses `Mzk1BoxActualR2Actual.W` and
`StepVDistinguishedSlotAverage.weightedAverage_collectionChoiceBound`.
-/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1BoxR2PerRowActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxActualR2Actual
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.IUTIV.StepVDistinguishedSlotAverage
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
universe u

theorem perRow_eq_collectionBound
    {E : Type u} [Fintype E] [Nonempty E]
    (lam : E → ℝ) (weights_pos : ∀ e, 0 < lam e)
    (l logp iotaL : ℝ) (l_ne_zero : l ≠ 0)
    (j : Nat) (d oq : E → ℝ) (slot : Fin (j + 1)) :
    (∑ t : Fin (j + 1) → E,
      collectionChoiceBound l logp iotaL j d oq t slot * W lam t) /
      (∑ t : Fin (j + 1) → E, W lam t) =
    collectionBound l ((∑ e, d e * logp * lam e) / ∑ e, lam e)
      ((∑ e, oq e * logp * lam e) / ∑ e, lam e) logp iotaL j :=
  weightedAverage_collectionChoiceBound lam weights_pos l logp iotaL l_ne_zero j d oq slot

#print axioms perRow_eq_collectionBound
end LeanFormal.IUT.XiFPaper.Mzk1BoxR2PerRowActual
end