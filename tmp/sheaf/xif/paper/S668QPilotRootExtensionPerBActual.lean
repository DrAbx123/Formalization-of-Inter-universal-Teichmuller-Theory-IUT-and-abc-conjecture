import tmp.sheaf.xif.paper.S312QPilotRootTensorBaseChangeActual
import tmp.sheaf.xif.paper.RootTensorHaarTransportActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual

/-! # S668: per-b qPilot -> rootNormedExtension map and product coordinate comparison

Actual map on each bad place:
  qVFamTensorBlock T b -> rootTensorBlock T b -> rootNormedExtension T b,
using the existing `qPilotBlockToRootTensor` and one-factor `blockLinearEquiv`.
The product side is compared only through the coordinate projection of
`RootExtensionProductImageHull`.  The containment/log inequality remains the
exact comparison, not a fabricated map between the full carriers.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S668QPilotRootExtensionPerBActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (cNorm : qVFamTensorV → Real)
variable (dataNorm : ArithmeticTuplePureFractionalScalingData
  (qVFamTensorPlaces T b) qVFamTensorTuple cNorm)

/-- Actual per-b map qVFam block -> rootNormedExtension. -/
noncomputable def qPilotToRootExtension :
    qVFamTensorBlock T b → rootNormedExtension T b :=
  fun x => blockLinearEquiv (l := l) T b (qPilotBlockToRootTensor (l := l) T b x)

theorem qPilotToRootExtension_eq (x : qVFamTensorBlock T b) :
    qPilotToRootExtension (l := l) T b x =
      blockLinearEquiv (l := l) T b (qPilotBlockToRootTensor (l := l) T b x) :=
  rfl

/-- Actual qPilot image in rootNormedExtension. -/
noncomputable def qPilotImageInRootExtension : Set (rootNormedExtension T b) :=
  qPilotToRootExtension (l := l) T b '' qPilotClassicalRegion
    (qVFamTensorPlaces T b) qVFamTensorTuple cNorm

/-- Product coordinate projection. -/
noncomputable def rootExtensionProductCoordinate :
    RootExtensionProductCarrier T → rootNormedExtension T b :=
  fun f => f b

/-- Coordinate projection of the actual root image hull. -/
noncomputable def rootImageCoordinate : Set (rootNormedExtension T b) :=
  rootExtensionProductCoordinate (l := l) T b '' rootExtensionProductImageHull T

/-- Per-b containment/log comparison interface. -/
structure QPilotPerBCoordinateComparison where
  qPilotImage : Set (rootNormedExtension T b)
  qPilotImage_eq : qPilotImage = qPilotImageInRootExtension (l := l) T b cNorm
  rootImageCoord_set : Set (rootNormedExtension T b)
  rootImageCoord_set_eq : rootImageCoord_set = rootImageCoordinate (l := l) T b
  containment : qPilotImage ⊆ rootImageCoord_set
  log_comparison : Prop
  log_comparison_proof : log_comparison

/-- Exact per-b containment proposition. -/
def QPilotPerBContainmentObstacle : Prop :=
  qPilotImageInRootExtension (l := l) T b cNorm ⊆ rootImageCoordinate (l := l) T b

/-- Conditional comparison from an explicit containment. -/
noncomputable def comparisonOfContainment
    (h : QPilotPerBContainmentObstacle (l := l) T b cNorm) :
    QPilotPerBCoordinateComparison (l := l) T b cNorm where
  qPilotImage := qPilotImageInRootExtension (l := l) T b cNorm
  qPilotImage_eq := rfl
  rootImageCoord_set := rootImageCoordinate (l := l) T b
  rootImageCoord_set_eq := rfl
  containment := h
  log_comparison := QPilotPerBContainmentObstacle (l := l) T b cNorm
  log_comparison_proof := h

def QPilotPerBCoordinateComparisonRequired : Prop :=
  Nonempty (QPilotPerBCoordinateComparison (l := l) T b cNorm)

end LeanFormal.IUT.XiFPaper.S668QPilotRootExtensionPerBActual
end
