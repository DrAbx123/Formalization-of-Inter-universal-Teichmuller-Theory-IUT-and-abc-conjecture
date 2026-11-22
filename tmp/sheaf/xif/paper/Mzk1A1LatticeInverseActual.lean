import tmp.sheaf.xif.paper.Mzk1P2LabelBlockCoefficientActual
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.PaperRootExtensionFieldScalingActual
/-! #A1 (A1.4): actual inverse lattice at one qVFam tensor block.

We work at a single actual block b.  qhat = lambda*c with c integral,
so qhat*O_L subset lambda*O_L; hence the inverse image lattice of
lambda*O_L under the actual embedding contains the q-lattice.  No comparison,
blockEquiv or delta-small hypothesis is used. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1A1LatticeInverseActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
/-- The lambda-lattice lambda * O_L. -/
def lambdaLattice : Set (rootNormedExtension T b) :=
  (fun y => rootThetaFieldLambda T b * y) '' rootExtensionUnitBall T b
/-- The qhat-lattice qhat * O_L. -/
def qhatLattice : Set (rootNormedExtension T b) :=
  (fun y => c0QHat T b * y) '' rootExtensionUnitBall T b
/-- Inverse image lattice of lambda * O_L inside the base field. -/
def inverseLambdaLattice : Set (rootBase T b) :=
  {x | algebraMap (rootBase T b) (rootNormedExtension T b) x ∈ lambdaLattice T b}
/-- qhat lies in the lambda-lattice because qhat = lambda*c with c integral. -/
theorem c0QHat_mem_lambdaLattice :
    c0QHat T b ∈ lambdaLattice T b := by
  refine ⟨p2Coefficient T b, p2Coefficient_mem_unitBall T b, ?_⟩
  rw [p2QHat_eq_lambda_mul_coefficient T b]
/-- The actual embedded q lies in the lambda-lattice. -/
theorem algebraMap_qVFamily_mem_lambdaLattice :
    algebraMap (rootBase T b) (rootNormedExtension T b)
        ((qVFamily T b).q : rootBase T b) ∈ lambdaLattice T b := by
  rw [← c0QHat_eq_q T b]
  exact c0QHat_mem_lambdaLattice T b
/-- qhat * O_L subset lambda * O_L (the A1.4 inclusion at the level of the
actual root lattice). -/
theorem qhatLattice_subset_lambdaLattice :
    qhatLattice T b ⊆ lambdaLattice T b := by
  rintro z ⟨y, hy, rfl⟩
  refine ⟨p2Coefficient T b * y, ?_, ?_⟩
  · unfold rootExtensionUnitBall at hy ⊢
    rw [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
    simp only [sub_zero] at hy ⊢
    rw [norm_mul]
    calc ‖p2Coefficient T b‖ * ‖y‖ ≤ 1 * 1 := by
          exact mul_le_mul (p2Coefficient_norm_le_one T b) hy (norm_nonneg _) zero_le_one
      _ = 1 := mul_one 1
  · rw [p2QHat_eq_lambda_mul_coefficient T b]
    ring
/-- The q-embedding lies in the inverse lambda-lattice (A1.4). -/
theorem qVFamily_mem_inverseLambdaLattice :
    ((qVFamily T b).q : rootBase T b) ∈ inverseLambdaLattice T b :=
  algebraMap_qVFamily_mem_lambdaLattice T b
end LeanFormal.IUT.XiFPaper.Mzk1A1LatticeInverseActual
end
