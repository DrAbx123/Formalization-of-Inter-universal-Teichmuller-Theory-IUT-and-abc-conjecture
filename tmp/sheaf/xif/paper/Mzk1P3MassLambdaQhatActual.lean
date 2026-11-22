import tmp.sheaf.xif.paper.Mzk1P3MassIdentificationActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3MassLambdaQhatActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P3MassIdentificationActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
noncomputable def lambdaMass (b : Bad (nativePlaceSelection T)) : ℝ :=
  Real.exp (Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖)
noncomputable def qhatMass (b : Bad (nativePlaceSelection T)) : ℝ :=
  Real.exp (Real.log ‖c0QHat T b‖)
theorem log_lambdaMass (b : Bad (nativePlaceSelection T)) :
    Real.log (lambdaMass T b) = Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ :=
  Real.log_exp _
theorem log_qhatMass (b : Bad (nativePlaceSelection T)) :
    Real.log (qhatMass T b) = Real.log ‖c0QHat T b‖ := Real.log_exp _
theorem lambdaQhat_logRatio (b : Bad (nativePlaceSelection T)) :
    Real.log (lambdaMass T b) - Real.log (qhatMass T b) =
      Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ - Real.log ‖c0QHat T b‖ := by
  rw [log_lambdaMass, log_qhatMass]
end LeanFormal.IUT.XiFPaper.Mzk1P3MassLambdaQhatActual
end