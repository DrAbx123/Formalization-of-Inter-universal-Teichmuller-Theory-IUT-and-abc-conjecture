import tmp.sheaf.xif.paper.S720OneFactorTensorNormReductionActual
import Mathlib.Analysis.Normed.Operator.LinearIsometry

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S757QVFamBlockIsometryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.LocalFieldPadicTensor
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Conditional isometry: if the two norm instances agree, the one-factor
tensor equivalence is a linear isometry equivalence. -/
noncomputable def qVFamBlockLinearIsometryEquiv
    (hpres : QVFamBlockNormPreserving (l := l) T b) :
    qVFamTensorBlock T b ≃ₗᵢ[ℚ_[qVFamTensorP T b]] rootBase T b where
  toLinearEquiv := qVFamBlockLinearEquiv (l := l) T b
  norm_map' := fun x => by
    exact (hpres x).symm

/-- The isometry's norm equality is exactly QVFamBlockNormPreserving. -/
theorem qVFamBlockLinearIsometryEquiv_norm_map
    (hpres : QVFamBlockNormPreserving (l := l) T b)
    (x : qVFamTensorBlock T b) :
    ‖(qVFamBlockLinearIsometryEquiv (l := l) T b hpres) x‖ = ‖x‖ :=
  (qVFamBlockLinearIsometryEquiv (l := l) T b hpres).norm_map x

/-- Exact norm-instance equality still needed. -/
def QVFamBlockNormEqualityRequired : Prop :=
  QVFamBlockNormPreserving (l := l) T b

end LeanFormal.IUT.XiFPaper.S757QVFamBlockIsometryActual

end
