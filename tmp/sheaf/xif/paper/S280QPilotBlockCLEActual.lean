import tmp.sheaf.xif.paper.S191QPilotCarrierTransportActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
/-! # S280: explicit per-b ContinuousLinearEquiv for the S191 block equivalence
Only the per-b def is built here.  NormedAddCommGroup/NormedSpace/
FiniteDimensional/CompleteSpace are supplied explicitly to avoid typeclass
search.  No product/transported statements yet. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
namespace LeanFormal.IUT.XiFPaper.S280QPilotBlockCLEActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.S191QPilotCarrierTransportActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (Block (G := sourceQGeometry (l := l) T b))]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (Block (G := sourceQGeometry (l := l) T b))]
/-- Explicit per-b continuous linear equivalence. -/
noncomputable def s191BlockCLE (b : Bad (nativePlaceSelection T)) :
    Block (G := sourceQGeometry (l := l) T b) ≃L[ℚ_[qVFamTensorP T b]]
      s191TensorFamily T b () := by
  letI : NormedAddCommGroup (Block (G := sourceQGeometry (l := l) T b)) :=
    inferInstance
  letI : NormedSpace ℚ_[qVFamTensorP T b]
      (Block (G := sourceQGeometry (l := l) T b)) := inferInstance
  letI : FiniteDimensional ℚ_[qVFamTensorP T b]
      (Block (G := sourceQGeometry (l := l) T b)) := inferInstance
  letI : CompleteSpace (Block (G := sourceQGeometry (l := l) T b)) :=
    FiniteDimensional.complete ℚ_[qVFamTensorP T b]
      (Block (G := sourceQGeometry (l := l) T b))
  letI : NormedAddCommGroup (s191TensorFamily T b ()) := inferInstance
  letI : NormedSpace ℚ_[qVFamTensorP T b] (s191TensorFamily T b ()) := inferInstance
  letI : FiniteDimensional ℚ_[qVFamTensorP T b] (s191TensorFamily T b ()) :=
    inferInstance
  letI : CompleteSpace (s191TensorFamily T b ()) :=
    FiniteDimensional.complete ℚ_[qVFamTensorP T b] (s191TensorFamily T b ())
  exact (s191BlockEquiv T b).toContinuousLinearEquivOfContinuous
    (LinearMap.continuous_of_finiteDimensional
      (𝕜 := ℚ_[qVFamTensorP T b])
      (E := Block (G := sourceQGeometry (l := l) T b))
      (F' := s191TensorFamily T b ())
      (s191BlockEquiv T b).toLinearMap)
end LeanFormal.IUT.XiFPaper.S280QPilotBlockCLEActual
