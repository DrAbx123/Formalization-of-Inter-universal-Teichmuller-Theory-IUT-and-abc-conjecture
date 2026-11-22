import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreCoeffAtPairSymmetryActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtValuesConsumerActual

universe u

theorem thetaCoeffAt_eq_consumer (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K n =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold thetaCoeffAt thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

theorem thetaCoeffAt_zero_consumer (K : Type u) [Field K] :
    thetaCoeffAt K 0 =
      HahnSeries.single (thetaUExponent 0) (1 : K) +
        HahnSeries.single (thetaUExponent (-1)) (-1 : K) := by
  rw [thetaCoeffAt_eq_consumer]
  simp [thetaUExponent, zpow_neg_one, zpow_zero]

theorem thetaCoeffAt_one_consumer (K : Type u) [Field K] :
    thetaCoeffAt K 1 =
      HahnSeries.single (thetaUExponent 1) (-1 : K) +
        HahnSeries.single (thetaUExponent (-2)) (1 : K) := by
  unfold thetaCoeffAt thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, thetaQExponent, thetaUExponent]
  norm_num

#check thetaCoeffAt_zero_consumer
#check thetaCoeffAt_one_consumer

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtValuesConsumerActual
