import tmp.sheaf.xif.paper.Mzk1ChangeMatrixActual
import Mathlib.LinearAlgebra.Matrix.Basis

/-! GAP-step: change-of-basis matrices form a groupoid (U*W=1, transitivity). -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ChangeMatrixRingActual
open Module
open LeanFormal.IUT.XiFPaper.Mzk1ChangeMatrixActual
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [Fintype ι] [DecidableEq ι]
theorem changeMatrix_mul (b b' b'' : Module.Basis ι R M) :
    changeMatrix b b' * changeMatrix b' b'' = changeMatrix b b'' :=
by simpa [changeMatrix] using
    Basis.toMatrix_mul_toMatrix (b := b) (b' := fun i => b' i) (b'' := fun i => b'' i)
theorem changeMatrix_mul_flip (b b' : Module.Basis ι R M) :
    changeMatrix b b' * changeMatrix b' b = 1 :=
by simpa [changeMatrix] using
    Basis.toMatrix_mul_toMatrix_flip (b := b) (b' := fun i => b' i)
theorem changeMatrix_one (b : Module.Basis ι R M) : changeMatrix b b = 1 :=
by simpa [changeMatrix] using Basis.toMatrix_self b
end LeanFormal.IUT.XiFPaper.Mzk1ChangeMatrixRingActual
end