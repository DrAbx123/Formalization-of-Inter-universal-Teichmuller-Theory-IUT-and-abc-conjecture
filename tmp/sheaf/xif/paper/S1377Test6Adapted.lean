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

example : W.preΨ 3 = W.Ψ₃ := by
  rw [show (3:ℤ) = ((3:ℕ):ℤ) by norm_num, WeierstrassCurve.preΨ_ofNat, WeierstrassCurve.preΨ'_three]

example : W.preΨ 4 = W.preΨ₄ := by
  rw [show (4:ℤ) = ((4:ℕ):ℤ) by norm_num, WeierstrassCurve.preΨ_ofNat, WeierstrassCurve.preΨ'_four]

end LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual
