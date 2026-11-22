import tmp.sheaf.xif.paper.Mzk1P6IVWeightsActual
import tmp.sheaf.xif.paper.Mzk1P6StepVAveragesActual
import tmp.sheaf.xif.paper.Mzk1P6IVActual
import tmp.sheaf.xif.paper.Mzk1P6IVDisplayAssemblyActual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
open LeanFormal.IUT LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open LeanFormal.IUT.XiFPaper.Mzk1P6IVWeightsActual
open LeanFormal.IUT.XiFPaper.Mzk1P6StepVAveragesActual
open LeanFormal.IUT.XiFPaper.Mzk1P6IVActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6IVInequalityActual
/-- Weighted two-sided form: the weighted StepV average of the actual readout
equals the collection bound. -/
theorem p6_iv_weightedAverage_collectionBound
    {E : Type*} [Fintype E] [Nonempty E]
    (lam : E → Real) (weights_pos : ∀ e, 0 < lam e)
    (l logp iotaL : Real) (l_ne_zero : l ≠ 0)
    (j : Nat) (d oq : E → Real) (slot : Fin (j + 1)) :
    (∑ et : Fin (j + 1) → E,
      collectionChoiceBound l logp iotaL j d oq et slot * ∏ i, lam (et i)) /
        (∑ et : Fin (j + 1) → E, ∏ i, lam (et i)) =
      collectionBound l ((∑ e, d e * logp * lam e) / ∑ e, lam e)
        ((∑ e, oq e * logp * lam e) / ∑ e, lam e) logp iotaL j :=
  p6_iv_weightedAverage lam weights_pos l logp iotaL l_ne_zero j d oq slot
/-- Weighted IV inequality: the actual stepped average readout obeys the
paper IV display inequality. -/
theorem p6_iv_weighted_inequality
    (n : Nat) (hn : 2 ≤ n) (D Q S T : Real)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (l : Real) (hl : l = 2 * (n : Real) + 1) :
    p6IVR n D Q S T ≤
      (l + 5) / 4 * p6IVD l D - (l + 1) / 24 * p6IVQ l Q +
        p6IVS l S + (l + 5) * p6IVT l T :=
  p6_iv_inequality n hn D Q S T hD hS hT l hl
#print axioms p6_iv_weightedAverage_collectionBound
#print axioms p6_iv_weighted_inequality
end LeanFormal.IUT.XiFPaper.Mzk1P6IVInequalityActual
end