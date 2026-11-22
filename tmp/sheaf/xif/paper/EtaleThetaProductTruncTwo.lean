import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaProductTruncTwo

universe u

noncomputable def etaleThetaProductTrunc (K : Type u) [Field K]
    (N : Nat) (q U : K) : K :=
  Finset.prod (Finset.range N) (fun m : Nat =>
    (1 - q ^ (2 * m + 2)) * (1 + U * q ^ (2 * m + 1)) *
      (1 + U⁻¹ * q ^ (2 * m + 1)))

theorem etaleThetaProductTrunc_two (K : Type u) [Field K] (q U : K) :
    etaleThetaProductTrunc K 2 q U =
      ((1 - q ^ 2) * (1 + U * q) * (1 + U⁻¹ * q)) *
        ((1 - q ^ 4) * (1 + U * q ^ 3) * (1 + U⁻¹ * q ^ 3)) := by
  simp [etaleThetaProductTrunc, Finset.prod_range_succ]

#check etaleThetaProductTrunc_two

end LeanFormal.IUT.XiFPaper.EtaleThetaProductTruncTwo
