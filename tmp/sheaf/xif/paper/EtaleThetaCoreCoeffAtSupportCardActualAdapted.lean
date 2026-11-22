import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreCoeffAtPairSymmetryActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtSupportCardActualAdapted

universe u

theorem thetaCoeffAt_eq_consumer (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K n =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold thetaCoeffAt thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

theorem thetaCoeffAt_support_subset_consumer (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).support ⊆ ({thetaUExponent n, thetaUExponent (-n - 1)} : Set Int) := by
  rw [thetaCoeffAt_eq_consumer]
  intro x hx
  rcases HahnSeries.support_add_subset _ _ hx with h | h
  · left; exact HahnSeries.support_single_subset h
  · right; exact HahnSeries.support_single_subset h

theorem thetaCoeffAt_coeff_u_consumer (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).coeff (thetaUExponent n) = (-1 : K) ^ n := by
  rw [thetaCoeffAt_eq_consumer]
  have hne : thetaUExponent n ≠ thetaUExponent (-n - 1) := by
    unfold thetaUExponent; omega
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne]

theorem thetaCoeffAt_coeff_neg_u_consumer (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).coeff (-thetaUExponent n) = (-1 : K) ^ (-n - 1) := by
  rw [thetaCoeffAt_eq_consumer]
  have hne : -thetaUExponent n ≠ thetaUExponent n := by
    unfold thetaUExponent; omega
  have hneg : thetaUExponent (-n - 1) = -thetaUExponent n := by
    unfold thetaUExponent; ring
  rw [hneg]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne]

theorem thetaCoeffAt_support_exact_consumer (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).support = ({thetaUExponent n, thetaUExponent (-n - 1)} : Set Int) := by
  apply Set.Subset.antisymm (thetaCoeffAt_support_subset_consumer K n)
  intro x hx
  rcases hx with hx | hx
  · rw [Set.mem_singleton_iff] at hx; subst x
    refine (HahnSeries.mem_support _ _).2 ?_
    rw [thetaCoeffAt_coeff_u_consumer]
    exact zpow_ne_zero n (by norm_num : (-1 : K) ≠ 0)
  · rw [Set.mem_singleton_iff] at hx; subst x
    refine (HahnSeries.mem_support _ _).2 ?_
    rw [thetaCoeffAt_coeff_neg_u_consumer]
    exact zpow_ne_zero (-n - 1) (by norm_num : (-1 : K) ≠ 0)

theorem thetaCoeffAt_support_encard_consumer (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).support.encard = 2 := by
  rw [thetaCoeffAt_support_exact_consumer]
  apply Set.encard_pair
  unfold thetaUExponent
  omega

#check thetaCoeffAt_support_encard_consumer

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtSupportCardActualAdapted
