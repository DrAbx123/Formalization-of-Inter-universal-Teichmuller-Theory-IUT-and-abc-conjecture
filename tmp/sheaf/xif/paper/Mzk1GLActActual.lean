import tmp.sheaf.xif.paper.Mzk1DiagEmbeddingEquivActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicIntegralLattice
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-! GAP-step: GL_d(Z_p) action preserves the integral coordinate lattice. -/
noncomputable section
open scoped LeanFormal.IUT.FinitePadicIntegralLattice
namespace LeanFormal.IUT.XiFPaper.Mzk1GLActActual
open LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
def glMatrix (g : Matrix.GeneralLinearGroup d (PadicInt p)) : Matrix d d ℚ_[p] :=
  fun i j => algebraMap (PadicInt p) ℚ_[p] (g i j)
def glAct (g : Matrix.GeneralLinearGroup d (PadicInt p)) (x : d → ℚ_[p]) : d → ℚ_[p] :=
  (glMatrix (p := p) g).mulVec x
theorem glAct_mem_coordSmall (g : Matrix.GeneralLinearGroup d (PadicInt p))
    {x : d → ℚ_[p]} (hx : x ∈ coordSmall (p := p) (d := d)) :
    glAct (p := p) g x ∈ coordSmall (p := p) (d := d) := by
  rw [coordSmall, Submodule.mem_pi] at hx ⊢
  intro i _
  simp only [glAct, glMatrix, Matrix.mulVec, dotProduct]
  apply Submodule.sum_mem
  intro j _
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (hx j (Set.mem_univ j))
end LeanFormal.IUT.XiFPaper.Mzk1GLActActual
end