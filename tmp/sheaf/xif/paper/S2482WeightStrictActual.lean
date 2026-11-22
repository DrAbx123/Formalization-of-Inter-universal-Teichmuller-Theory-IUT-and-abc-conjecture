import tmp.sheaf.xif.paper.S2482WeightAdditivityActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482WeightStrictActual

open LeanFormal.IUT.XiFPaper.S2482OrderTwoAlgAutClassificationActualV2
open LeanFormal.IUT.XiFPaper.S2482WeightAdditivityActual
open Polynomial

lemma coords_neg (z : A) :
    coords (-z) = (-(coords z).1, -(coords z).2) := by
  apply coords_eq_of_eq
  have h := congrArg Neg.neg (coords_spec z)
  simpa [neg_smul, add_neg, add_comm] using h

lemma W_neg (z : A) : W (-z) = W z := by
  rw [W_eq, W_eq, coords_neg]
  simp

lemma W_add_eq_of_lt (z w : A) (h : W z < W w) :
    W (z + w) = W w := by
  refine le_antisymm ?_ ?_
  · calc W (z + w) ≤ max (W z) (W w) := W_add_le z w
      _ = W w := max_eq_right h.le
  · by_contra hnot
    have hlt : W (z + w) < W w := lt_of_not_ge hnot
    have hw : W w ≤ max (W (z + w)) (W (-z)) := by
      have hh := W_add_le (z + w) (-z)
      have hsum : (z + w) + -z = w := by abel
      rwa [hsum] at hh
    have hmax : max (W (z + w)) (W (-z)) < W w := by
      rw [W_neg]
      exact max_lt hlt h
    exact (not_le_of_gt hmax) hw

theorem W_add_eq_max_of_ne (z w : A) (h : W z ≠ W w) :
    W (z + w) = max (W z) (W w) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [W_add_eq_of_lt z w hlt, max_eq_right hlt.le]
  · rw [add_comm, W_add_eq_of_lt w z hgt, max_eq_left hgt.le]


end LeanFormal.IUT.XiFPaper.S2482WeightStrictActual
end