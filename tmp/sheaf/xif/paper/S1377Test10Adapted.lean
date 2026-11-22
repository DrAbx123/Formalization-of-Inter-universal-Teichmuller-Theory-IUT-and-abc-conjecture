import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

lemma w_recursion_algebra {a b c d e g x u X : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hxu : x - u = a * c / b ^ 2)
    (hXu : X - u = - e / (a ^ 2 * b ^ 2)) :
    (g * (u - X) - (d / b ^ 4) * (x - X)) / (x - u) =
      - (d / b ^ 4) + (g - d / b ^ 4) * (e / (a ^ 3 * c)) := by
  have h1 : u - X = e / (a ^ 2 * b ^ 2) := by linear_combination -hXu
  have hxX : x - X = a * c / b ^ 2 + e / (a ^ 2 * b ^ 2) := by
    linear_combination hxu + h1
  rw [hxX, h1, hxu]
  field_simp [ha, hb, hc]
  ring

end LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual
