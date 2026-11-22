import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaProductTruncOne

universe u

noncomputable def etaleThetaProductTrunc (K : Type u) [Field K]
    (N : Nat) (q U : K) : K :=
  Finset.prod (Finset.range N) (fun m : Nat =>
    (1 - q ^ (2 * m + 2)) * (1 + U * q ^ (2 * m + 1)) *
      (1 + U⁻¹ * q ^ (2 * m + 1)))

theorem etaleThetaProductTrunc_one (K : Type u) [Field K] (q U : K) :
    etaleThetaProductTrunc K 1 q U =
      (1 - q ^ 2) * (1 + U * q) * (1 + U⁻¹ * q) := by
  simp [etaleThetaProductTrunc]

theorem etaleThetaProductTrunc_zero (K : Type u) [Field K] (q U : K) :
    etaleThetaProductTrunc K 0 q U = 1 := by
  simp [etaleThetaProductTrunc]

#check etaleThetaProductTrunc_one
#check etaleThetaProductTrunc_zero

end LeanFormal.IUT.XiFPaper.EtaleThetaProductTruncOne
