import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncDiffPairNonzeroActualAdapted

universe u

theorem thetaPairTerm_coeff_at (K : Type u) [Field K] (n : Int) :
    (thetaPairTerm K n).coeff (thetaQExponent n) =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

theorem thetaPairTerm_ne_zero (K : Type u) [Field K] (n : Int) :
    thetaPairTerm K n ≠ 0 := by
  intro h
  have hc := congrArg (fun s : HahnSeries HalfInt (HahnSeries Int K) => s.coeff (thetaQExponent n)) h
  rw [thetaPairTerm_coeff_at] at hc
  have hne : thetaUExponent n ≠ thetaUExponent (-n - 1) := by
    unfold thetaUExponent; omega
  have hinner := congrArg (fun s : HahnSeries Int K => s.coeff (thetaUExponent n)) hc
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne] at hinner
  exact (zpow_ne_zero n (by norm_num : (-1 : K) ≠ 0)) hinner

theorem etaleThetaSymmetricTrunc_diff_exact (K : Type u) [Field K] (N : Nat) :
    etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N =
      thetaPairTerm K (N + 1 : Int) := by
  rw [etaleThetaSymmetricTrunc_succ]
  exact add_sub_cancel_left _ _

theorem etaleThetaSymmetricTrunc_diff_ne_zero (K : Type u) [Field K] (N : Nat) :
    etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N ≠ 0 := by
  rw [etaleThetaSymmetricTrunc_diff_exact]
  exact thetaPairTerm_ne_zero K (N + 1 : Int)

#check thetaPairTerm_ne_zero
#check etaleThetaSymmetricTrunc_diff_ne_zero

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncDiffPairNonzeroActualAdapted
