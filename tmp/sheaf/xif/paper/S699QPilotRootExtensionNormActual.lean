import tmp.sheaf.xif.paper.S678QPilotRootExtensionOperatorBoundActual
import Mathlib.Analysis.Normed.Algebra.Basic

/-! # S699: norm analysis of qPilotToRootExtension

`blockNorm_eq` identifies the norm on `rootTensorBlock` with the norm on
`rootNormedExtension`.  The base inclusion `rootBase -> rootNormedExtension` is
isometric because the ambient is a NormedAlgebra over rootBase.
Thus the qPilot map has the same norm as `qVFamBlockLinearEquiv x`; the only
remaining norm comparison is whether that one-factor tensor equivalence is an
isometry.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S699QPilotRootExtensionNormActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S668QPilotRootExtensionPerBActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- The base inclusion rootBase -> rootNormedExtension is an isometry. -/
theorem norm_algebraMap_rootBase_rootNormedExtension
    (a : rootBase T b) :
    ‖(algebraMap (rootBase T b) (rootNormedExtension T b) a :
      rootNormedExtension T b)‖ = ‖a‖ := by
  change ‖(algebraMap (rootBase T b) (rootNormedAmbient T b) a :
      rootNormedAmbient T b)‖ = ‖a‖
  exact norm_algebraMap' (rootNormedAmbient T b) a

/-- Norm of the actual qPilot map equals the norm of the one-factor tensor
equivalence image. -/
theorem qPilotToRootExtension_norm_eq (x : qVFamTensorBlock T b) :
    ‖qPilotToRootExtension (l := l) T b x‖ =
      ‖(qVFamBlockLinearEquiv (l := l) T b x : rootBase T b)‖ := by
  rw [qPilotToRootExtension, qPilotBlockToRootTensor]
  rw [LinearEquiv.apply_symm_apply]
  exact norm_algebraMap_rootBase_rootNormedExtension (l := l) T b _

/-- Exact norm-isometry condition for the one-factor tensor equivalence. -/
def QVFamBlockNormIsometry : Prop :=
  ∀ x : qVFamTensorBlock T b,
    ‖(qVFamBlockLinearEquiv (l := l) T b x : rootBase T b)‖ = ‖x‖

/-- If the one-factor tensor equivalence is an isometry, the qPilot map has
operator constant one. -/
theorem qPilotToRootExtension_norm_eq_norm_of_isometry
    (h : QVFamBlockNormIsometry (l := l) T b) (x : qVFamTensorBlock T b) :
    ‖qPilotToRootExtension (l := l) T b x‖ = ‖x‖ := by
  rw [qPilotToRootExtension_norm_eq]
  exact h x

/-- Exact remaining norm-comparison datum. -/
def QVFamBlockNormComparisonObstacle : Prop :=
  QVFamBlockNormIsometry (l := l) T b

end LeanFormal.IUT.XiFPaper.S699QPilotRootExtensionNormActual
end
