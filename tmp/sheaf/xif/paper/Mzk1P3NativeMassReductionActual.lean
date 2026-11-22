import tmp.sheaf.xif.paper.Mzk1P3MassIdentificationActual
/-! P3 (R3.7): weighted native mass difference reduces exactly to the P2 R1.3
correction `p2R13Exact` once the blockwise native identification holds. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P3NativeMassReductionActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P3MassIdentificationActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1S1915DegreeFinrankActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Degree-weighted native L-side log mass. -/
noncomputable def nativeWeightedLogMassL : ℝ :=
  ∑ b : Bad (nativePlaceSelection T),
    (s1915LocalDegree T b : ℝ) * nativeThetaReadout T b
/-- Degree-weighted native Q-side log mass. -/
noncomputable def nativeWeightedLogMassQ : ℝ :=
  ∑ b : Bad (nativePlaceSelection T),
    (s1915LocalDegree T b : ℝ) * nativeQReadout T b
/-- Blockwise native identification implies the weighted R1.3 identity. -/
theorem nativeWeightedMassDifference_eq_p2R13_of_blockwise
    (h : ∀ b : Bad (nativePlaceSelection T),
      R37R13NativeMassIdentification T b) :
    nativeWeightedLogMassL T - nativeWeightedLogMassQ T = p2R13Exact T := by
  unfold nativeWeightedLogMassL nativeWeightedLogMassQ
  rw [← Finset.sum_sub_distrib]
  rw [p2R13Exact_eq_sum_blockTerms]
  apply Finset.sum_congr rfl
  intro b _
  have hb := h b
  unfold R37R13NativeMassIdentification at hb
  have hlog : nativeThetaReadout T b - nativeQReadout T b =
      - Real.log ‖p2Coefficient T b‖ := by
    rw [hb, p2_log_lambda_sub_log_qhat T b]
  unfold p2R13BlockTerm
  rw [← mul_sub, hlog]

/-- Exact missing: a single blockwise native identification is not implied by the
global sum identity (only the converse is proved); tensor/product carrier
alignment is required (see `p2NativeProductBlockMissing`). -/
def blockwiseMissingReason : String :=
  "global weighted identity <= pointwise native identification; converse needs native tensor block to product-carrier alignment"
end LeanFormal.IUT.XiFPaper.Mzk1P3NativeMassReductionActual
end