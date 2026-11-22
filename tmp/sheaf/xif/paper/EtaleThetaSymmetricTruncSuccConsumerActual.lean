import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccConsumerActual

universe u

theorem etaleThetaSymmetricTrunc_succ_consumer (K : Type u) [Field K] (N : Nat) :
    etaleThetaSymmetricTrunc K (N + 1) =
      etaleThetaSymmetricTrunc K N + thetaPairTerm K (N + 1 : Int) :=
  etaleThetaSymmetricTrunc_succ K N

theorem etaleThetaSymmetricTrunc_succ_coeff_consumer (K : Type u) [Field K]
    (N : Nat) (e : HalfInt) :
    (etaleThetaSymmetricTrunc K (N + 1)).coeff e =
      (etaleThetaSymmetricTrunc K N).coeff e +
        (thetaPairTerm K (N + 1 : Int)).coeff e := by
  rw [etaleThetaSymmetricTrunc_succ_consumer, HahnSeries.coeff_add]

theorem etaleThetaSymmetricTrunc_diff_support_consumer (K : Type u) [Field K] (N : Nat) :
    (etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N).support ⊆
      ({thetaQExponent (N + 1 : Int)} : Set HalfInt) :=
  etaleThetaSymmetricTrunc_diff_support K N

theorem etaleThetaSymmetricTrunc_coeff_stable_consumer (K : Type u) [Field K]
    (N : Nat) (e : HalfInt) (h : e ≠ thetaQExponent (N + 1 : Int)) :
    (etaleThetaSymmetricTrunc K (N + 1)).coeff e =
      (etaleThetaSymmetricTrunc K N).coeff e :=
  etaleThetaSymmetricTrunc_coeff_stable K N e h

#check etaleThetaSymmetricTrunc_succ_coeff_consumer
#check etaleThetaSymmetricTrunc_diff_support_consumer
#check etaleThetaSymmetricTrunc_coeff_stable_consumer

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccConsumerActual
