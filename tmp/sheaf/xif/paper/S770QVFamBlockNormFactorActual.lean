import tmp.sheaf.xif.paper.S757QVFamBlockIsometryActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S770QVFamBlockNormFactorActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S757QVFamBlockIsometryActual
open LeanFormal.IUT.LocalFieldPadicTensor
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- The coordinate norm on the qVFam tensor block. -/
noncomputable def qVFamBlockCoordinateNorm
    (x : qVFamTensorBlock T b) : Real :=
  ‖finitePadicTensorCoordinates (p := qVFamTensorP T b)
    (fun i => CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i))) x‖

/-- The tensor norm is the coordinate norm (definition of the induced norm). -/
theorem qVFamBlock_tensor_norm_eq_coordinate
    (x : qVFamTensorBlock T b) :
    ‖x‖ = qVFamBlockCoordinateNorm (l := l) T b x := by
  rfl

/-- The rootBase norm of the image. -/
noncomputable def qVFamBlockRootNorm
    (x : qVFamTensorBlock T b) : Real :=
  ‖qVFamBlockLinearEquiv (l := l) T b x‖

/-- Exact norm factor (ratio) between the tensor norm and the rootBase norm. -/
noncomputable def qVFamBlockNormRatio
    (x : qVFamTensorBlock T b) : Real :=
  qVFamBlockCoordinateNorm (l := l) T b x /
    qVFamBlockRootNorm (l := l) T b x

/-- Norm preservation is exactly ratio one on nonzero vectors. -/
theorem qVFamBlockNormPreserving_iff_ratio_one :
    QVFamBlockNormPreserving (l := l) T b ↔
      ∀ x : qVFamTensorBlock T b, x ≠ 0 →
        qVFamBlockCoordinateNorm (l := l) T b x =
          qVFamBlockRootNorm (l := l) T b x := by
  unfold QVFamBlockNormPreserving qVFamBlockRootNorm
  constructor
  · intro h x hx
    exact h x
  · intro h x
    by_cases hx : x = 0
    · subst hx
      simp [qVFamBlockCoordinateNorm, qVFamBlockRootNorm]
    · exact h x hx

/-- Exact norm equality goal, no inhabitant. -/
def QVFamBlockNormEqualityGoal : Prop :=
  QVFamBlockNormPreserving (l := l) T b

end LeanFormal.IUT.XiFPaper.S770QVFamBlockNormFactorActual

end
