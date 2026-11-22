import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncDiffPairZeroActualAdapted

universe u

theorem etaleThetaSymmetricTrunc_diff_exact (K : Type u) [Field K] (N : Nat) :
    etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N =
      thetaPairTerm K (N + 1 : Int) := by
  rw [etaleThetaSymmetricTrunc_succ]
  exact add_sub_cancel_left _ _

theorem etaleThetaSymmetricTrunc_diff_sub_pair_zero (K : Type u) [Field K] (N : Nat) :
    (etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N) -
      thetaPairTerm K (N + 1 : Int) = 0 := by
  rw [etaleThetaSymmetricTrunc_diff_exact]
  abel

#check etaleThetaSymmetricTrunc_diff_sub_pair_zero

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncDiffPairZeroActualAdapted
