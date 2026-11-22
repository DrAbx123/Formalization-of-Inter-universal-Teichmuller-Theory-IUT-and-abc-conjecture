import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncDiffSupportExactConsumerActualAdapted

universe u

theorem thetaPairTerm_coeff_at (K : Type u) [Field K] (n : Int) :
    (thetaPairTerm K n).coeff (thetaQExponent n) =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

theorem thetaPairTerm_coeff_at_ne_zero (K : Type u) [Field K] (n : Int) :
    (thetaPairTerm K n).coeff (thetaQExponent n) ≠ 0 := by
  rw [thetaPairTerm_coeff_at]
  intro h
  have hc := congrArg (fun s : HahnSeries Int K => s.coeff (thetaUExponent n)) h
  have hne : thetaUExponent n ≠ thetaUExponent (-n - 1) := by
    unfold thetaUExponent; omega
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne] at hc
  exact (zpow_ne_zero n (by norm_num : (-1 : K) ≠ 0)) hc

theorem thetaPairTerm_support_exact (K : Type u) [Field K] (n : Int) :
    (thetaPairTerm K n).support = ({thetaQExponent n} : Set HalfInt) := by
  apply Set.Subset.antisymm (thetaPairTerm_support K n)
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  exact (HahnSeries.mem_support _ _).2 (thetaPairTerm_coeff_at_ne_zero K n)

theorem etaleThetaSymmetricTrunc_diff_exact (K : Type u) [Field K] (N : Nat) :
    etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N =
      thetaPairTerm K (N + 1 : Int) := by
  rw [etaleThetaSymmetricTrunc_succ]
  exact add_sub_cancel_left _ _

theorem etaleThetaSymmetricTrunc_diff_support_exact_consumer
    (K : Type u) [Field K] (N : Nat) :
    (etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N).support =
      ({thetaQExponent (N + 1 : Int)} : Set HalfInt) := by
  rw [etaleThetaSymmetricTrunc_diff_exact]
  exact thetaPairTerm_support_exact K (N + 1 : Int)

#check etaleThetaSymmetricTrunc_diff_support_exact_consumer

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncDiffSupportExactConsumerActualAdapted
