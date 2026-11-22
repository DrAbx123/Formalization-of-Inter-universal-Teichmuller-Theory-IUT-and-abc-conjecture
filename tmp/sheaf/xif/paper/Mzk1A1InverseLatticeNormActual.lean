import tmp.sheaf.xif.paper.Mzk1A1LatticeInverseActual
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeV2Actual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
/-! #A1.5: actual inverse-lattice norm description.

`lambdaLattice = lambda*O_L` is exactly the closed norm ball of radius `||lambda||`;
hence the inverse lambda-lattice is `{x : rootBase | ||algebraMap x|| <= ||lambda||}`.
Similarly the qhat-lattice is the closed ball of radius `||qhat||`.  This is the
norm-level identification of J_s; the remaining pi_F^{ceil(m/e)} step is the
ramification/valuation half (no extra hypothesis is introduced here). -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1A1InverseLatticeNormActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1A1LatticeInverseActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Norm description of the lambda-lattice. -/
theorem mem_lambdaLattice_iff (y : rootNormedExtension T b) :
    y ∈ lambdaLattice T b ↔ ‖y‖ ≤ ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ := by
  have hlampos : 0 < ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ := by
    rw [← rootImageRadius_eq_norm_fieldLambda]
    exact_mod_cast rootImageRadius_pos (T := T) (b := b)
  have hlamne : rootThetaFieldLambda T b ≠ 0 := norm_ne_zero_iff.mp hlampos.ne'
  constructor
  · rintro ⟨o, ho, rfl⟩
    have ho' : ‖o‖ ≤ 1 := by
      simpa [rootExtensionUnitBall, Metric.mem_closedBall, dist_eq_norm] using ho
    rw [norm_mul]
    calc ‖rootThetaFieldLambda T b‖ * ‖o‖ ≤ ‖rootThetaFieldLambda T b‖ * 1 := by
          exact mul_le_mul_of_nonneg_left ho' (norm_nonneg _)
      _ = ‖rootThetaFieldLambda T b‖ := mul_one _
  · intro hy
    refine ⟨y / rootThetaFieldLambda T b, ?_, ?_⟩
    · unfold rootExtensionUnitBall
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_div]
      exact (div_le_one hlampos).mpr hy
    · field_simp [hlamne]
/-- Norm description of the qhat-lattice. -/
theorem mem_qhatLattice_iff (y : rootNormedExtension T b) :
    y ∈ qhatLattice T b ↔ ‖y‖ ≤ ‖c0QHat T b‖ := by
  have hqne : c0QHat T b ≠ 0 := by
    unfold c0QHat
    exact pow_ne_zero _ (c0Alpha_ne_zero T b)
  have hqpos : 0 < ‖c0QHat T b‖ := norm_pos_iff.mpr hqne
  constructor
  · rintro ⟨o, ho, rfl⟩
    have ho' : ‖o‖ ≤ 1 := by
      simpa [rootExtensionUnitBall, Metric.mem_closedBall, dist_eq_norm] using ho
    rw [norm_mul]
    calc ‖c0QHat T b‖ * ‖o‖ ≤ ‖c0QHat T b‖ * 1 := by
          exact mul_le_mul_of_nonneg_left ho' (norm_nonneg _)
      _ = ‖c0QHat T b‖ := mul_one _
  · intro hy
    refine ⟨y / c0QHat T b, ?_, ?_⟩
    · unfold rootExtensionUnitBall
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_div]
      exact (div_le_one hqpos).mpr hy
    · field_simp [hqne]
/-- The inverse lambda-lattice is the algebraMap norm ball. -/
theorem inverseLambdaLattice_eq_normBall :
    inverseLambdaLattice T b =
      {x : rootBase T b |
        ‖algebraMap (rootBase T b) (↑(rootNormedExtension T b)) x‖ ≤
          ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖} := by
  ext x
  rw [show x ∈ inverseLambdaLattice T b ↔
      algebraMap (rootBase T b) (↑(rootNormedExtension T b)) x ∈ lambdaLattice T b
    from Iff.rfl, mem_lambdaLattice_iff]
  rfl
/-- The qhat norm is at most the lambda norm, hence the qhat ball is contained
in the lambda ball. -/
theorem qhatBall_subset_lambdaBall :
    {y : ↑(rootNormedExtension T b) | ‖y‖ ≤ ‖c0QHat T b‖} ⊆
      {y : ↑(rootNormedExtension T b) |
        ‖y‖ ≤ ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖} := by
  intro y hy
  have hqle : ‖c0QHat T b‖ ≤
      ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ := by
    rw [← rootImageRadius_eq_norm_fieldLambda]
    exact c0QHat_norm_le_radius T b
  exact hy.trans hqle
end LeanFormal.IUT.XiFPaper.Mzk1A1InverseLatticeNormActual
end