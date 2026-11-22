import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreCoeffAtPairSymmetryActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtSupportEqActualAdapted

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

theorem thetaCoeffAt_coeff_u_ne_zero (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).coeff (thetaUExponent n) ≠ 0 := by
  rw [thetaCoeffAt_eq_local]
  have hne : thetaUExponent n ≠ thetaUExponent (-n - 1) := by
    unfold thetaUExponent; omega
  rw [HahnSeries.coeff_add, HahnSeries.coeff_single, HahnSeries.coeff_single]
  simp [hne]
  exact zpow_ne_zero n (by norm_num : (-1 : K) ≠ 0)

theorem thetaCoeffAt_coeff_neg_u_ne_zero (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).coeff (-thetaUExponent n) ≠ 0 := by
  rw [thetaCoeffAt_eq_local]
  have hne : -thetaUExponent n ≠ thetaUExponent n := by
    unfold thetaUExponent; omega
  have hneg : thetaUExponent (-n - 1) = -thetaUExponent n := by
    unfold thetaUExponent; ring
  rw [hneg, HahnSeries.coeff_add, HahnSeries.coeff_single, HahnSeries.coeff_single]
  simp [hne]
  exact zpow_ne_zero (-n - 1) (by norm_num : (-1 : K) ≠ 0)

theorem thetaCoeffAt_mem_support_u (K : Type u) [Field K] (n : Int) :
    thetaUExponent n ∈ (thetaCoeffAt K n).support :=
  (HahnSeries.mem_support _ _).2 (thetaCoeffAt_coeff_u_ne_zero K n)

theorem thetaCoeffAt_mem_support_neg_u (K : Type u) [Field K] (n : Int) :
    -thetaUExponent n ∈ (thetaCoeffAt K n).support :=
  (HahnSeries.mem_support _ _).2 (thetaCoeffAt_coeff_neg_u_ne_zero K n)

theorem thetaCoeffAt_support_eq (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).support = ({thetaUExponent n, -thetaUExponent n} : Set Int) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases thetaCoeffAt_support_subset_local K n hx with h | h
    · left; exact h
    · right
      rw [h]
      unfold thetaUExponent
      ring
  · intro x hx
    rcases hx with h | h
    · subst x
      exact thetaCoeffAt_mem_support_u K n
    · rw [Set.mem_singleton_iff] at h
      subst x
      exact thetaCoeffAt_mem_support_neg_u K n

#check thetaCoeffAt_support_eq

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtSupportEqActualAdapted
