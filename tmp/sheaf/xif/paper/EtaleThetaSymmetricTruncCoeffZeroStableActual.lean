import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffZeroStableActual

universe u

theorem thetaQExponent_nat_ne_zero (N : Nat) :
    thetaQExponent (N + 1 : Int) ≠ 0 := by
  unfold thetaQExponent
  have h : (0 : Rat) < ((N : Rat) + 1) := by positivity
  have h' : (0 : Rat) < ((N : Rat) + 2) := by positivity
  positivity

theorem etaleThetaSymmetricTrunc_coeff_zero_constant (K : Type u) [Field K] (M : Nat) :
    (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc K M).coeff
        (0 : HalfInt) =
      (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc K 0).coeff
        (0 : HalfInt) := by
  induction M with
  | zero => rfl
  | succ M ih =>
      rw [LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc_coeff_stable K M 0]
      · exact ih
      · exact (thetaQExponent_nat_ne_zero M).symm

theorem etaleThetaSymmetricTrunc_coeff_zero_value (K : Type u) [Field K] (M : Nat) :
    (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc K M).coeff
        (0 : HalfInt) =
      HahnSeries.single (thetaUExponent 0) (1 : K) +
        HahnSeries.single (thetaUExponent (-1)) (-1 : K) := by
  rw [etaleThetaSymmetricTrunc_coeff_zero_constant]
  simp [LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc,
    LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaPairTerm,
    LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaTermEx,
    thetaQExponent, thetaUExponent]
  norm_num

theorem etaleThetaSymmetricTrunc_coeff_zero_ne_zero (K : Type u) [Field K] (M : Nat) :
    (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc K M).coeff
        (0 : HalfInt) ≠ 0 := by
  rw [etaleThetaSymmetricTrunc_coeff_zero_value]
  intro h
  have hc := congrArg (fun s : HahnSeries Int K => s.coeff (1 : Int)) h
  have hne : (1 : Int) ≠ -1 := by norm_num
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne] at hc

#check etaleThetaSymmetricTrunc_coeff_zero_constant
#check etaleThetaSymmetricTrunc_coeff_zero_value

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffZeroStableActual
