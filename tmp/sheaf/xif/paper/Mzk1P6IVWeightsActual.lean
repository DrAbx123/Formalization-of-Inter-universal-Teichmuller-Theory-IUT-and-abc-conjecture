/- P6 IV weighted-average/reindex consumer from actual StepV averages. -/
import LeanFormal.IUT.IUTIV.Estimates.StepVDistinguishedSlotAverage
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
namespace LeanFormal.IUT.XiFPaper.Mzk1P6IVWeightsActual
variable {E : Type*} [Fintype E] [Nonempty E]
theorem p6_iv_weightedAverage
    (lam : E → Real) (weights_pos : ∀ e, 0 < lam e)
    (l logp iotaL : Real) (l_ne_zero : l ≠ 0)
    (j : Nat) (d oq : E → Real) (slot : Fin (j + 1)) :
    (∑ et : Fin (j + 1) → E,
      collectionChoiceBound l logp iotaL j d oq et slot * ∏ i, lam (et i)) /
      (∑ et : Fin (j + 1) → E, ∏ i, lam (et i)) =
    collectionBound l ((∑ e, d e * logp * lam e) / ∑ e, lam e)
      ((∑ e, oq e * logp * lam e) / ∑ e, lam e) logp iotaL j :=
  LeanFormal.IUT.IUTIV.StepVDistinguishedSlotAverage.weightedAverage_collectionChoiceBound
    lam weights_pos l logp iotaL l_ne_zero j d oq slot
#print axioms p6_iv_weightedAverage
end LeanFormal.IUT.XiFPaper.Mzk1P6IVWeightsActual
