import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreCoeffAtPairSymmetryActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtNonzeroConsumerActual

universe u

theorem thetaCoeffAt_eq_consumer (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K n =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold thetaCoeffAt thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

theorem thetaCoeffAt_ne_zero_consumer (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K n ≠ 0 := by
  intro h
  have hc := congrArg (fun s : HahnSeries Int K => s.coeff (thetaUExponent n)) h
  rw [thetaCoeffAt_eq_consumer] at hc
  have hne : thetaUExponent n ≠ thetaUExponent (-n - 1) := by
    unfold thetaUExponent; omega
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne] at hc
  exact (zpow_ne_zero n (by norm_num : (-1 : K) ≠ 0)) hc

#check thetaCoeffAt_ne_zero_consumer

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtNonzeroConsumerActual
