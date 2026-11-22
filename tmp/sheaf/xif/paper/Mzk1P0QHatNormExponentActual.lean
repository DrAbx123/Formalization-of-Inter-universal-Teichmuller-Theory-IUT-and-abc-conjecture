/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.Mzk1P2QNativeSourceArrowActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import Mathlib.Tactic
/-! # P0.6 gap②: qhat norm = residueNormBase^(-exponent) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0QHatNormExponentActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P2QNativeSourceArrowActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
theorem c0QHat_norm_eq_residueNormBase_zpow :
    ‖c0QHat T b‖ =
      residueNormBase ((nativeBadLift T).lift b) ^ (-(qVFamily T b).exponent : Int) := by
  have hq' : ‖c0QHat T b‖ =
      ‖((qVFamily T b).q :
        LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual.rootBase T b)‖ := by
    rw [c0QHat_eq_q T b]
    exact norm_algebraMap' (rootNormedExtension T b)
      ((qVFamily T b).q :
        LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual.rootBase T b)
  rw [hq']
  exact qNorm_eq_residueNormBase_zpow (qVFamily T b)
theorem c0QHat_log_eq_exponent :
    Real.log ‖c0QHat T b‖ =
      -((qVFamily T b).exponent : Real) *
        Real.log (residueNormBase ((nativeBadLift T).lift b)) := by
  rw [c0QHat_norm_eq_residueNormBase_zpow T b, Real.log_zpow]
  ring
end LeanFormal.IUT.XiFPaper.Mzk1P0QHatNormExponentActual
end
