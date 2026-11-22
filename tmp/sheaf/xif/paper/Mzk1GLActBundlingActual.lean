/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1MatrixHaarBaseActual

/-! # glAct bundled as a Q_p-linear map (task-109, green step) -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1GLActBundlingActual
open LeanFormal.IUT.XiFPaper.Mzk1MatrixHaarBaseActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
/-- The matrix action as a Q_p-linear map. -/
noncomputable def glLinear (V : Matrix d d (PadicInt p)) :
    (d → ℚ_[p]) →ₗ[ℚ_[p]] (d → ℚ_[p]) :=
  Matrix.mulVecLin (glMatrix p d V)
theorem glLinear_apply (V : Matrix d d (PadicInt p)) (x : d → ℚ_[p]) :
    glLinear V x = glAct p d V x := rfl
def bundlingRows : List (String × String) :=
  [ ("glLinear", "Q_p-linear action"),
    ("continuous/equivalence", "GAP") ]
theorem bundlingRows_length : bundlingRows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1GLActBundlingActual
