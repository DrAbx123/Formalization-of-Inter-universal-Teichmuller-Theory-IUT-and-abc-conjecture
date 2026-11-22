import tmp.sheaf.xif.paper.S671QPilotRadiusAuditActual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S683QPilotRadiusOperatorAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S671QPilotRadiusAuditActual
open LeanFormal.IUT.XiFPaper.S668QPilotRootExtensionPerBActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable (cNorm : qVFamTensorV → Real)
variable (dataNorm : ArithmeticTuplePureFractionalScalingData
  (qVFamTensorPlaces T b) qVFamTensorTuple cNorm)

/-- Same conditional lemma with a source operator constant C directly. -/
theorem qPilotRadiusBound_of_operatorConstant
    (C : Real) (hCnonneg : 0 ≤ C)
    (hC : ∀ x : qVFamTensorBlock T b,
      ‖qPilotToRootExtension (l := l) T b x‖ ≤ C * ‖x‖)
    (R : Real)
    (hregion : ∀ x : qVFamTensorBlock T b,
      x ∈ qPilotClassicalRegion (qVFamTensorPlaces T b) qVFamTensorTuple cNorm →
        ‖x‖ ≤ R)
    (hbound : C * R ≤ (rootImageRadius T b : Real)) :
    QPilotRadiusBoundObstacle (l := l) T b cNorm := by
  intro x hx
  calc
    ‖qPilotToRootExtension (l := l) T b x‖ ≤ C * ‖x‖ := hC x
    _ ≤ C * R := mul_le_mul_of_nonneg_left (hregion x hx) hCnonneg
    _ ≤ (rootImageRadius T b : Real) := hbound

end LeanFormal.IUT.XiFPaper.S683QPilotRadiusOperatorAuditActual

end
