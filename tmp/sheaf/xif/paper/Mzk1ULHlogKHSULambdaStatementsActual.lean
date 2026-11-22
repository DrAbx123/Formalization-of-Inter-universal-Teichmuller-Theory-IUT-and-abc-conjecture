/- 轻件: hlogK_wild / hsQ_per_place 的 λ 版 statement 层（无重 import）。
  J1/C3-upper 的字母接口: 外层权 w（=thetaLamWeight）、逐项 D_b（log dK 项）、
  hlogdK_λ / hsQraw_λ 的精确形状，由 hlogK/hsQ 真证填入（不 fake）。 -/
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHlogKHSULambdaStatementsActual

universe u

/-- hlogdK 的 λ 权形状: Σ_i w_i·D_i ≤ S_ar + 2 log l + 21（paper L1425 +21 版）。 -/
structure HlogKLambdaData (ι : Type u) [Fintype ι] where
  w : ι → ℝ
  D : ι → ℝ
  S_ar : ℝ
  logl : ℝ
  hlogdK : (∑ i, w i * D i) ≤ S_ar + 2 * Real.log logl + 21

/-- hsQraw 的 λ 权形状: (Σ_i w_i)·log s≤ ≤ 2 d_mod S_ar + 5 + log l（paper L1572/L1573）。 -/
structure HsQrawLambdaData (ι : Type u) [Fintype ι] where
  w : ι → ℝ
  logSleq : ℝ
  dmod : ℝ
  S_ar : ℝ
  logl : ℝ
  hsQraw : (∑ i, w i) * logSleq ≤ 2 * dmod * S_ar + 5 * 1 + Real.log logl

/-- hlogK_wild 的逐位接口: δ_i ≤ e_i(κ_i+1) ⇒ log 项 ≤ 21 + 2log l 的形状由组装者给。 -/
structure WildBoundData where
  delta : ℕ
  e : ℕ
  kappa : ℕ
  hdelta : delta < e * (kappa + 1)

/-- 从 λ 字母得到 hlogdK 的形状（re-export，供 C3 组装）。 -/
theorem hlogK_lambda_shape {ι : Type u} [Fintype ι] (D : HlogKLambdaData ι) :
    (∑ i, D.w i * D.D i) ≤ D.S_ar + 2 * Real.log D.logl + 21 := D.hlogdK

/-- 从 λ 字母得到 hsQraw 的形状。 -/
theorem hsQraw_lambda_shape {ι : Type u} [Fintype ι] (D : HsQrawLambdaData ι) :
    (∑ i, D.w i) * D.logSleq ≤ 2 * D.dmod * D.S_ar + 5 + Real.log D.logl := by
  have := D.hsQraw
  simpa using this

#print axioms hlogK_lambda_shape
#print axioms hsQraw_lambda_shape

end LeanFormal.IUT.XiFPaper.Mzk1ULHlogKHSULambdaStatementsActual