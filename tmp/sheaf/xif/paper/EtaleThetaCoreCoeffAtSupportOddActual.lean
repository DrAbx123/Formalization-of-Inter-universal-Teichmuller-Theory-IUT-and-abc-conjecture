import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreCoeffAtPairSymmetryActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtSupportOddActual

universe u

theorem thetaCoeffAt_eq_local (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K n =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold thetaCoeffAt thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

theorem thetaCoeffAt_support_subset_local (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).support ⊆ ({thetaUExponent n, thetaUExponent (-n - 1)} : Set Int) := by
  rw [thetaCoeffAt_eq_local]
  intro x hx
  rcases HahnSeries.support_add_subset _ _ hx with h | h
  · left; exact HahnSeries.support_single_subset h
  · right; exact HahnSeries.support_single_subset h

theorem thetaCoeffAt_support_odd (K : Type u) [Field K] (n : Int) (x : Int)
    (hx : x ∈ (thetaCoeffAt K n).support) :
    exists m : Int, x = 2 * m + 1 := by
  rcases thetaCoeffAt_support_subset_local K n hx with h | h
  · refine ⟨n, ?_⟩
    rw [h]
    unfold thetaUExponent
    ring
  · refine ⟨-n - 1, ?_⟩
    rw [h]
    unfold thetaUExponent
    ring

#check thetaCoeffAt_support_odd

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtSupportOddActual
