import LeanFormal.IUT.Foundations.Geometry.TateCurve
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Group.Ultra

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LeanFormal.IUT.PAdicAnalytic

universe u

variable {K : Type u} [NormedField K] [CharZero K] [IsUltrametricDist K] [CompleteSpace K]

/-- The canonical Tate q-series j-invariant `j(q) = c4(q)^3 / Delta(q)`. -/
noncomputable def tateJK (q : K) : K :=
  (TateCurve.weierstrassCurve K q).c₄ ^ 3 /
    (TateCurve.weierstrassCurve K q).Δ

/-- The canonical inverse-j parameter `H(q) = Delta(q) / c4(q)^3`. -/
noncomputable def tateHK (q : K) : K :=
  (TateCurve.weierstrassCurve K q).Δ /
    (TateCurve.weierstrassCurve K q).c₄ ^ 3

/-- The canonical j/H relation: `H(q) * j(q) = 1` when `c4` and `Delta` are nonzero. -/
theorem tateHK_mul_tateJK (q : K)
    (hc4 : (TateCurve.weierstrassCurve K q).c₄ ≠ 0)
    (hΔ : (TateCurve.weierstrassCurve K q).Δ ≠ 0) :
    tateHK q * tateJK q = 1 := by
  unfold tateHK tateJK
  field_simp [hc4, hΔ, pow_ne_zero 3 hc4]

/-- The inverse-j parameter is the field inverse of the canonical j-invariant. -/
theorem tateHK_eq_inv_tateJK (q : K)
    (hc4 : (TateCurve.weierstrassCurve K q).c₄ ≠ 0)
    (hΔ : (TateCurve.weierstrassCurve K q).Δ ≠ 0) :
    tateHK q = (tateJK q)⁻¹ := by
  unfold tateHK tateJK
  field_simp [hc4, hΔ, pow_ne_zero 3 hc4]

end LeanFormal.IUT.PAdicAnalytic
