import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreCoeffAtPairSymmetryActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtValuesNonzeroActual

universe u

theorem thetaCoeffAt_eq_consumer (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K n =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold thetaCoeffAt thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

theorem thetaCoeffAt_zero_ne_zero (K : Type u) [Field K] :
    thetaCoeffAt K 0 ≠ 0 := by
  intro h
  have hc := congrArg (fun s : HahnSeries Int K => s.coeff (thetaUExponent 0)) h
  rw [thetaCoeffAt_eq_consumer] at hc
  have hne : thetaUExponent 0 ≠ thetaUExponent (-1) := by
    unfold thetaUExponent; norm_num
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne] at hc

theorem thetaCoeffAt_one_ne_zero (K : Type u) [Field K] :
    thetaCoeffAt K 1 ≠ 0 := by
  intro h
  have hc := congrArg (fun s : HahnSeries Int K => s.coeff (thetaUExponent 1)) h
  rw [thetaCoeffAt_eq_consumer] at hc
  have hne : thetaUExponent 1 ≠ thetaUExponent (-2) := by
    unfold thetaUExponent; norm_num
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne] at hc

#check thetaCoeffAt_zero_ne_zero
#check thetaCoeffAt_one_ne_zero

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtValuesNonzeroActual
