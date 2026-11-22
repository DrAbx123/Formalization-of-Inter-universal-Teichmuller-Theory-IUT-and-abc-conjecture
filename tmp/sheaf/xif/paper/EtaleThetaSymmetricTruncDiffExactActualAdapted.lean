import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncDiffExactActualAdapted

universe u

theorem etaleThetaSymmetricTrunc_diff_exact (K : Type u) [Field K] (N : Nat) :
    etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N =
      thetaPairTerm K (N + 1 : Int) := by
  rw [etaleThetaSymmetricTrunc_succ]
  exact add_sub_cancel_left _ _

theorem etaleThetaSymmetricTrunc_diff_coeff_exact (K : Type u) [Field K]
    (N : Nat) (e : HalfInt) :
    (etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N).coeff e =
      (thetaPairTerm K (N + 1 : Int)).coeff e := by
  rw [etaleThetaSymmetricTrunc_diff_exact]

#check etaleThetaSymmetricTrunc_diff_exact
#check etaleThetaSymmetricTrunc_diff_coeff_exact

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncDiffExactActualAdapted
