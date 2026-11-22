/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1MatrixHaarBaseActual
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # GL_d(Z_p) to ContinuousLinearEquiv packaging (task-109) -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1GLActContinuousActual
open LeanFormal.IUT.XiFPaper.Mzk1MatrixHaarBaseActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]

/-- Send an integral invertible matrix to a continuous Q_p-linear automorphism
of the coordinate space. -/
noncomputable def glContinuousLinearEquiv
    (V : Matrix.GeneralLinearGroup d (PadicInt p)) :
    (d → ℚ_[p]) ≃L[ℚ_[p]] (d → ℚ_[p]) := by
  let VQ : Matrix.GeneralLinearGroup d ℚ_[p] :=
    Matrix.GeneralLinearGroup.map (algebraMap (PadicInt p) ℚ_[p]) V
  let e : (d → ℚ_[p]) ≃ₗ[ℚ_[p]] (d → ℚ_[p]) :=
    (Matrix.GeneralLinearGroup.toLin (n := d) (R := ℚ_[p]) VQ).toLinearEquiv
  exact e.toContinuousLinearEquiv

def glContinuousRows : List (String × String) :=
  [ ("glContinuousLinearEquiv", "matrix GL -> continuous linear equiv"),
    ("action = glAct", "GAP"),
    ("apply canonical full map_eq", "GAP") ]
theorem glContinuousRows_length : glContinuousRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1GLActContinuousActual
