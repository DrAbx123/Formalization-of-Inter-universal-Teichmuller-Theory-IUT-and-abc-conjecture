/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib
import tmp.sheaf.xif.paper.Mzk1HullExactScalingQpilotActual

open LeanFormal.IUT.XiFPaper.Mzk1HullExactScalingQpilotActual

/-! # Mzk1BadInvScalingLawQpilotActual — bad-place inverse scaling law (A659)

Scaling laws for the bad-place `λ`-direction of the triple-dependent candidate
`λ = a+b+c+1` (as a real scalar): the natural-number scaling is the real scalar
scaling, its norm is multiplicative, and the inverse scaling is exact
(`λ⁻¹ • λ • x = x`), with the closed-ball inverse scaling formula. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1BadInvScalingLawQpilotActual

universe u

/-- Natural-number scaling is real scalar scaling in a real normed space. -/
theorem nsmul_eq_real_smul {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (n : Nat) (x : E) : n • x = (n : Real) • x := by
  rw [← Nat.cast_smul_eq_nsmul Real n x]

/-- Norm of the scalar scaling is multiplicative. -/
theorem norm_real_smul {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (lam : Real) (x : E) : ‖lam • x‖ = ‖lam‖ * ‖x‖ := norm_smul lam x

/-- Exact inverse scaling: `λ⁻¹ • (λ • x) = x` for `λ ≠ 0`. -/
theorem inv_scale_exact {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (lam : Real) (hlam : lam ≠ 0) (x : E) : lam⁻¹ • (lam • x) = x := by
  rw [smul_smul, inv_mul_cancel₀ hlam, one_smul]

/-- Norm of the inverse scaling. -/
theorem norm_inv_scale {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (lam : Real) (x : E) : ‖lam⁻¹ • x‖ = ‖lam‖⁻¹ * ‖x‖ := by
  rw [norm_smul, norm_inv]

/-- Inverse closed-ball scaling: `λ⁻¹`-scaling rescales the radius by `‖λ‖⁻¹`. -/
theorem closedBall_inv_scale_exact {k : Type u} [NormedField k]
    (lam : k) (hlam : lam ≠ 0) (R : Real) :
    (fun x : k => lam⁻¹ * x) '' Metric.closedBall (0 : k) R =
      Metric.closedBall (0 : k) (‖lam‖⁻¹ * R) := by
  have h := closedBall_scale_exact (k := k) lam⁻¹ (inv_ne_zero hlam) R
  simpa [norm_inv] using h

/-- Law rows for the bad-place inverse scaling. -/
def badInvScalingRows : List (String × String) :=
  [ ("nsmul = real smul", "PROVED"),
    ("norm multiplicative", "PROVED"),
    ("inverse scaling exact", "PROVED"),
    ("closed-ball inverse scaling", "PROVED") ]

theorem badInvScalingRows_length : badInvScalingRows.length = 4 := rfl

#check nsmul_eq_real_smul
#check closedBall_inv_scale_exact
#check badInvScalingRows_length

end LeanFormal.IUT.XiFPaper.Mzk1BadInvScalingLawQpilotActual
end
