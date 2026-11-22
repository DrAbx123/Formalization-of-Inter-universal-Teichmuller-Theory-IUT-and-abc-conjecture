import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaProductTruncQZero

universe u

noncomputable def etaleThetaProductTrunc (K : Type u) [Field K]
    (N : Nat) (q U : K) : K :=
  Finset.prod (Finset.range N) (fun m : Nat =>
    (1 - q ^ (2 * m + 2)) * (1 + U * q ^ (2 * m + 1)) *
      (1 + U⁻¹ * q ^ (2 * m + 1)))

theorem etaleThetaProductTrunc_q_zero (K : Type u) [Field K]
    (N : Nat) (U : K) :
    etaleThetaProductTrunc K N 0 U = 1 := by
  simp [etaleThetaProductTrunc]

#check etaleThetaProductTrunc_q_zero

end LeanFormal.IUT.XiFPaper.EtaleThetaProductTruncQZero
