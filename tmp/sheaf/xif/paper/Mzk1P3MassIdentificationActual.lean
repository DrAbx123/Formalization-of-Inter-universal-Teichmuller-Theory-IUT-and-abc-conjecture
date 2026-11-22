import tmp.sheaf.xif.paper.Mzk1P3NetGainLogActual
import tmp.sheaf.xif.paper.Mzk1P3NetGainSourceGapActual
import tmp.sheaf.xif.paper.Mzk1S1915DegreeFinrankActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.Mzk1P3NetGainP2Actual
import tmp.sheaf.xif.paper.Mzk1P2DetWeightedNonnegActual
import tmp.sheaf.xif.paper.Mzk1P2QNativeSourceArrowActual
import tmp.sheaf.xif.paper.Mzk1P2NativeBlockAlignmentActual
import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
/-! P3 (R3.7): mass identification between native tensor readouts and the P2
root `lambda/qhat` data.  Reductions are proved; the remaining tensor/product
carrier alignment is recorded as the exact missing donor (shared with P2). -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P3MassIdentificationActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
open LeanFormal.IUT.XiFPaper.Mzk1P2QNativeSourceArrowActual
open LeanFormal.IUT.XiFPaper.Mzk1P2NativeBlockAlignmentActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1P3NetGainLogActual
open LeanFormal.IUT.XiFPaper.Mzk1P3NetGainSourceGapActual
open LeanFormal.IUT.XiFPaper.Mzk1S1915DegreeFinrankActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.Mzk1P3NetGainP2Actual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Native L-side mass: exponential of the native tensor log-volume. -/
noncomputable def nativeMassL (b : Bad (nativePlaceSelection T)) : ℝ :=
  Real.exp (nativeThetaReadout T b)
/-- Native Q-side mass: exponential of the native q readout. -/
noncomputable def nativeMassQ (b : Bad (nativePlaceSelection T)) : ℝ :=
  Real.exp (nativeQReadout T b)
theorem log_nativeMassL (b : Bad (nativePlaceSelection T)) :
    Real.log (nativeMassL T b) = nativeThetaReadout T b :=
  Real.log_exp _
theorem log_nativeMassQ (b : Bad (nativePlaceSelection T)) :
    Real.log (nativeMassQ T b) = nativeQReadout T b :=
  Real.log_exp _
/-- P2 R1.3 block term `d_b * (-log ‖c_b‖)`. -/
noncomputable def p2R13BlockTerm (b : Bad (nativePlaceSelection T)) : ℝ :=
  (s1915LocalDegree T b : ℝ) * (- Real.log ‖p2Coefficient T b‖)
/-- The R1.3 weighted mass difference is the sum of block terms. -/
theorem p2R13Exact_eq_sum_blockTerms :
    p2R13Exact T = ∑ b : Bad (nativePlaceSelection T), p2R13BlockTerm T b := by
  unfold p2R13Exact p2R13MassDifference p2R13BlockTerm
  apply Finset.sum_congr rfl
  intro b _
  rw [p2_log_lambda_sub_log_qhat T b]
/-- Exact native mass identification at one bad place. -/
def R37R13NativeMassIdentification (b : Bad (nativePlaceSelection T)) : Prop :=
  nativeThetaReadout T b - nativeQReadout T b =
    Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ -
      Real.log ‖c0QHat T b‖
/-- The native mass identification is exactly the P2 coefficient identity. -/
theorem R37R13NativeMassIdentification_iff_coefficient
    (b : Bad (nativePlaceSelection T)) :
    R37R13NativeMassIdentification T b ↔
      nativeThetaReadout T b - nativeQReadout T b =
        - Real.log ‖p2Coefficient T b‖ := by
  unfold R37R13NativeMassIdentification
  rw [p2_log_lambda_sub_log_qhat T b]
/-- If the native block identification holds, the abstract R3.7 mass
identification holds with the native masses and root `lambda/qhat`. -/
theorem R37R13MassIdentification_native_of_block
    (b : Bad (nativePlaceSelection T))
    (h : R37R13NativeMassIdentification T b) :
    R37R13MassIdentification
      (nativeMassL T b) (nativeMassQ T b)
      ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ ‖c0QHat T b‖ := by
  change Real.log (nativeMassL T b) - Real.log (nativeMassQ T b) =
    Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ -
      Real.log ‖c0QHat T b‖
  have h' := h
  unfold R37R13NativeMassIdentification at h'
  rw [log_nativeMassL, log_nativeMassQ]
  exact h'
def massIdentificationMissing : List String :=
  [ "native tensor block over base completions vs product of root extensions (p2NativeProductBlockMissing)",
    "native q signed log reading vs log norm of c0QHat (P2QNativeReadingGap shape)",
    "native tensor log-volume vs weighted sum of block log norm lambda",
    "det/tensor-product factor: share GAP-DET-HAAR donor from qpilot route" ]
theorem massIdentificationMissing_length : massIdentificationMissing.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P3MassIdentificationActual
end