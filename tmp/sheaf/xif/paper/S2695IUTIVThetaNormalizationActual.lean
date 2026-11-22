import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage

noncomputable section
open Finset
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2695IUTIVThetaNormalizationActual

open LeanFormal.IUT.IUTIV.StepVProcessionAverage

/-- IUT IV Step (v), theta-only specialization: for `l = 2n+1`, the
procession average over `j = 1,...,n` of `-j^2/(2l)·Q` is
`-(l+1)/24·Q`.  Here `Q = log q_{vQ}` is the IUT IV q-log. -/
theorem S2695_IUTIV_theta_average (n : ℕ) (hn : 1 ≤ n) (Q : ℝ) :
    (1 / (n : ℝ)) *
        ∑ j ∈ Icc 1 n, collectionBound (2 * (n : ℝ) + 1) 0 Q 0 0 j =
      -(((2 * (n : ℝ) + 1) + 1) / 24) * Q := by
  have h := processionAverage_eq n hn 0 Q 0 0
  simpa using h

/-- At `l = 5` (`n = 2`), the IUT IV theta-only average is `-Q/4`. -/
theorem S2695_IUTIV_theta_average_five (Q : ℝ) :
    (1 / 2) *
        ∑ j ∈ Icc 1 2, collectionBound 5 0 Q 0 0 j =
      -Q / 4 := by
  have h := S2695_IUTIV_theta_average 2 (by norm_num) Q
  norm_num at h
  rw [h]
  ring

/-- At the actual Gaussian parameter `q = 1/5`, so `Q = log q = -log 5`,
the IUT IV theta-only signed average at `l = 5` is `(log 5)/4`. -/
theorem S2695_IUTIV_theta_average_five_inv_five :
    (1 / 2) *
        ∑ j ∈ Icc 1 2,
          collectionBound 5 0 (Real.log ((5 : ℝ)⁻¹)) 0 0 j =
      Real.log 5 / 4 := by
  rw [S2695_IUTIV_theta_average_five, Real.log_inv]
  ring

#check S2695_IUTIV_theta_average
#check S2695_IUTIV_theta_average_five
#check S2695_IUTIV_theta_average_five_inv_five
#print axioms S2695_IUTIV_theta_average_five_inv_five

end LeanFormal.IUT.XiFPaper.S2695IUTIVThetaNormalizationActual
end
