import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaProductTrunc

universe u

/-- Finite truncation of the [EtTh] theta product side:
    q_X^{2m+2}, U q_X^{2m+1}, U^{-1} q_X^{2m+1}. -/
noncomputable def etaleThetaProductTrunc (K : Type u) [Field K]
    (N : Nat) (q U : K) : K :=
  Finset.prod (Finset.range N) (fun m : Nat =>
    (1 - q ^ (2 * m + 2)) * (1 + U * q ^ (2 * m + 1)) *
      (1 + U⁻¹ * q ^ (2 * m + 1)))

theorem etaleThetaProductTrunc_succ (K : Type u) [Field K]
    (N : Nat) (q U : K) :
    etaleThetaProductTrunc K (N + 1) q U =
      etaleThetaProductTrunc K N q U *
        ((1 - q ^ (2 * N + 2)) * (1 + U * q ^ (2 * N + 1)) *
          (1 + U⁻¹ * q ^ (2 * N + 1))) := by
  simp [etaleThetaProductTrunc, Finset.prod_range_succ]

#check etaleThetaProductTrunc
#check etaleThetaProductTrunc_succ

end LeanFormal.IUT.XiFPaper.EtaleThetaProductTrunc
