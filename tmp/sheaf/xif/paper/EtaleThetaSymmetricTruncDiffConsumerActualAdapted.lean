import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncDiffConsumerActualAdapted

universe u

theorem etaleThetaSymmetricTrunc_diff_coeff_eq_zero_consumer
    (K : Type u) [Field K] (N : Nat) (e : HalfInt)
    (h : e ≠ thetaQExponent (N + 1 : Int)) :
    (etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N).coeff e = 0 :=
  etaleThetaSymmetricTrunc_diff_coeff_eq_zero K N e h

theorem etaleThetaSymmetricTrunc_diff_support_singleton_consumer
    (K : Type u) [Field K] (N : Nat) :
    (etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N).support ⊆
      ({thetaQExponent (N + 1 : Int)} : Set HalfInt) :=
  etaleThetaSymmetricTrunc_diff_support K N

#check etaleThetaSymmetricTrunc_diff_coeff_eq_zero_consumer
#check etaleThetaSymmetricTrunc_diff_support_singleton_consumer

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncDiffConsumerActualAdapted
