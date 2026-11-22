import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncDiffCoeffZeroActualAdapted

universe u

theorem etaleThetaSymmetricTrunc_diff_exact (K : Type u) [Field K] (N : Nat) :
    etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N =
      thetaPairTerm K (N + 1 : Int) := by
  rw [etaleThetaSymmetricTrunc_succ]
  exact add_sub_cancel_left _ _

theorem etaleThetaSymmetricTrunc_diff_coeff_zero (K : Type u) [Field K]
    (N : Nat) (e : HalfInt) (h : e ≠ thetaQExponent (N + 1 : Int)) :
    (etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N).coeff e = 0 := by
  rw [etaleThetaSymmetricTrunc_diff_exact]
  by_contra hc
  have hmem : e ∈ (thetaPairTerm K (N + 1 : Int)).support := (HahnSeries.mem_support _ _).2 hc
  exact h (Set.mem_singleton_iff.mp (thetaPairTerm_support K (N + 1 : Int) hmem))

#check etaleThetaSymmetricTrunc_diff_coeff_zero

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncDiffCoeffZeroActualAdapted
