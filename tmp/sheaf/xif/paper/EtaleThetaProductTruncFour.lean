import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaProductTruncFour

universe u

noncomputable def etaleThetaProductTrunc (K : Type u) [Field K]
    (N : Nat) (q U : K) : K :=
  Finset.prod (Finset.range N) (fun m : Nat =>
    (1 - q ^ (2 * m + 2)) * (1 + U * q ^ (2 * m + 1)) *
      (1 + U⁻¹ * q ^ (2 * m + 1)))

theorem etaleThetaProductTrunc_four (K : Type u) [Field K] (q U : K) :
    etaleThetaProductTrunc K 4 q U =
      ((1 - q ^ 2) * (1 + U * q) * (1 + U⁻¹ * q)) *
        ((1 - q ^ 4) * (1 + U * q ^ 3) * (1 + U⁻¹ * q ^ 3)) *
          ((1 - q ^ 6) * (1 + U * q ^ 5) * (1 + U⁻¹ * q ^ 5)) *
            ((1 - q ^ 8) * (1 + U * q ^ 7) * (1 + U⁻¹ * q ^ 7)) := by
  simp [etaleThetaProductTrunc, Finset.prod_range_succ]

#check etaleThetaProductTrunc_four

end LeanFormal.IUT.XiFPaper.EtaleThetaProductTruncFour
