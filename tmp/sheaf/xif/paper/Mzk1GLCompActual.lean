import tmp.sheaf.xif.paper.Mzk1GLActActual

/-! GAP-step: composition law for the GL_d(Z_p) action. -/
noncomputable section
open scoped LeanFormal.IUT.FinitePadicIntegralLattice
namespace LeanFormal.IUT.XiFPaper.Mzk1GLCompActual
open LeanFormal.IUT.XiFPaper.Mzk1GLActActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
theorem glMatrix_mul (g h : Matrix.GeneralLinearGroup d (PadicInt p)) :
    glMatrix (p := p) (g * h) = glMatrix (p := p) g * glMatrix (p := p) h := by
  ext i j
  simp [glMatrix, Matrix.mul_apply, map_sum, map_mul]

theorem glAct_comp (g h : Matrix.GeneralLinearGroup d (PadicInt p))
    (x : d → ℚ_[p]) :
    glAct (p := p) g (glAct (p := p) h x) = glAct (p := p) (g * h) x := by
  simp only [glAct]
  rw [Matrix.mulVec_mulVec, ← glMatrix_mul]
end LeanFormal.IUT.XiFPaper.Mzk1GLCompActual
end