import tmp.sheaf.xif.paper.Mzk1P3MassIdentificationActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3SourceComparisonAttemptActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P3MassIdentificationActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Reduces source comparison to the native block mass identification. -/
theorem sourceComparison_of_native_block (massK massQ : ℝ)
    (b : Bad (nativePlaceSelection T))
    (h : R37R13NativeMassIdentification T b) :
    Real.log (nativeMassL T b) - Real.log (nativeMassQ T b) +
        (Real.log massK - Real.log massQ) =
      (Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ -
        Real.log ‖c0QHat T b‖) + (Real.log massK - Real.log massQ) := by
  rw [log_nativeMassL, log_nativeMassQ]
  have h' := h
  unfold R37R13NativeMassIdentification at h'
  rw [h']
end LeanFormal.IUT.XiFPaper.Mzk1P3SourceComparisonAttemptActual
end