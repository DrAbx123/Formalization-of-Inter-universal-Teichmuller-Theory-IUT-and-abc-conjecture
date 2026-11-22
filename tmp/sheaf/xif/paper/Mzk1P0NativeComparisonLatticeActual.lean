/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeV2Actual
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.PaperRootExtensionFieldScalingActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import Mathlib.Tactic
/-! #1: A1 lattice/norm route to native comparison (no product-carrier alignment) -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeComparisonLatticeActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- Norm bridge: the root qhat norm is the native q norm. -/
theorem c0QHat_norm_eq_qVFamily_norm :
    ‖c0QHat T b‖ = ‖((qVFamily T b).q : rootBase T b)‖ := by
  rw [c0QHat_eq_q T b]
  exact norm_algebraMap' (rootNormedExtension T b)
    ((qVFamily T b).q : rootBase T b)
/-- The qhat norm is at most the lambda norm (A1 lattice coefficient is integral). -/
theorem c0QHat_norm_le_lambda :
    ‖c0QHat T b‖ ≤ ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ := by
  have h := c0QHat_norm_le_radius T b
  rwa [rootImageRadius_eq_norm_fieldLambda] at h
/-- Native q readout is exactly the (negative) log norm. -/
theorem nativeQReadout_eq_log_norm :
    nativeQReadout T b = Real.log ‖(qVFamily T b).q‖ := by
  unfold nativeQReadout
  rw [abs_of_neg (Real.log_neg (qNorm_pos (qVFamily T b)) (qNorm_lt_one (qVFamily T b)))]
  ring
/-- Pointwise upper bound: native q readout <= log of the lambda norm. -/
theorem nativeQReadout_le_log_lambda :
    nativeQReadout T b ≤
      Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ := by
  rw [nativeQReadout_eq_log_norm]
  apply Real.log_le_log (qNorm_pos (qVFamily T b))
  calc ‖(qVFamily T b).q‖ = ‖c0QHat T b‖ :=
        (c0QHat_norm_eq_qVFamily_norm T b).symm
    _ ≤ ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ :=
        c0QHat_norm_le_lambda T b
/-- Exact remaining interface: theta readout vs log of lambda norm. -/
def NativeThetaLogLambdaBridge : Prop :=
  Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ ≤
    nativeThetaReadout T b
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeComparisonLatticeActual
end
