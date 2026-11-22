import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffZeroConsumerActualAdapted

universe u

theorem thetaQExponent_nat_ne_zero (N : Nat) :
    thetaQExponent (N + 1 : Int) ≠ 0 := by
  unfold thetaQExponent
  have h : (0 : Rat) < ((N : Rat) + 1) := by positivity
  have h' : (0 : Rat) < ((N : Rat) + 2) := by positivity
  positivity

theorem thetaPairTerm_zero_coeff (K : Type u) [Field K] :
    (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaPairTerm K 0).coeff (0 : HalfInt) =
      HahnSeries.single (thetaUExponent 0) (1 : K) +
        HahnSeries.single (thetaUExponent (-1)) (-1 : K) := by
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaPairTerm
    LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, thetaQExponent, thetaUExponent]
  norm_num

theorem etaleThetaSymmetricTrunc_coeff_zero_all (K : Type u) [Field K] (N : Nat) :
    (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc K N).coeff
        (0 : HalfInt) =
      HahnSeries.single (thetaUExponent 0) (1 : K) +
        HahnSeries.single (thetaUExponent (-1)) (-1 : K) := by
  induction N with
  | zero =>
      simp [LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc]
      exact thetaPairTerm_zero_coeff K
  | succ N ih =>
      rw [LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc_coeff_stable K N 0]
      · exact ih
      · exact (thetaQExponent_nat_ne_zero N).symm

#check etaleThetaSymmetricTrunc_coeff_zero_all

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffZeroConsumerActualAdapted
