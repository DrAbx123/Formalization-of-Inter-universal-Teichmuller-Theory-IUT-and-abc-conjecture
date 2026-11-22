import tmp.sheaf.xif.paper.RootNormalizedThetaHullActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

/-! # qPilot root region inside the root Theta hull

The root theta hull is rootThetaHull = closure (union_j rootThetaRegion j).
The q-pilot root region is the j = 1 root region

  qPilotRootRegion = rootThetaRegion oneSignedLabel.

It is contained in the union and hence in the closure hull.  The actual
normalized log-volume qPilotRootRegionLogVolume is therefore <= the root hull
log-volume whenever the actual Haar positivity/finiteness fields hold
(arithmeticTupleNormalizedLogVolume_mono).  The qPilot root coefficient formula
is recorded separately; no equality of the root hull log-volume with the
formula is asserted.

No fake inequality/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVPilotRootRegionNestingActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.RootNormalizedThetaHullActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual q-pilot root region: the root theta region at j = 1. -/
noncomputable def qPilotRootRegion : Set (qVFamTensorBlock T b) :=
  rootThetaRegion T b (oneSignedLabel (l := l))

/-- The q-pilot root region is contained in the root image union. -/
theorem qPilotRootRegion_subset_rootThetaImageSet :
    qPilotRootRegion T b ⊆ rootThetaImageSet T b := by
  intro x hx
  unfold rootThetaImageSet
  exact Set.mem_iUnion.mpr ⟨oneSignedLabel (l := l), hx⟩

/-- The q-pilot root region is contained in the root theta hull (closure). -/
theorem qPilotRootRegion_subset_rootThetaHull :
    qPilotRootRegion T b ⊆ rootThetaHull T b :=
  (qPilotRootRegion_subset_rootThetaImageSet T b).trans
    (subset_closure)

/-- Actual normalized log-volume of the q-pilot root region. -/
noncomputable def qPilotRootRegionLogVolume
    [MeasurableSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b)) : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
    qVFamTensorTuple mu (qPilotRootRegion T b)

/-- Actual normalized log-volume of the root theta hull. -/
noncomputable def rootThetaHullLogVolume
    [MeasurableSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b)) : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
    qVFamTensorTuple mu (rootThetaHull T b)

/-- Actual lower-bound direction: qPilot root region log-volume is at most the
root hull log-volume, under the actual Haar positivity/finiteness conditions. -/
theorem qPilotRootRegionLogVolume_le_rootThetaHullLogVolume
    [MeasurableSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b))
    (hSpos : 0 < mu (qPilotRootRegion T b))
    (hTfin : mu (rootThetaHull T b) < ⊤) :
    qPilotRootRegionLogVolume T b mu ≤ rootThetaHullLogVolume T b mu :=
  arithmeticTupleNormalizedLogVolume_mono
    (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (qPilotRootRegion_subset_rootThetaHull T b) hSpos hTfin

/-- Actual q-pilot root coefficient formula log at the j=1 minimal sector. -/
noncomputable def qPilotRootRegionFormulaLog : Real :=
  - (∑ _ : qVFamTensorV, rootThetaCoefficient T b
      (oneSignedLabel (l := l)) ()) *
      Real.log (qVFamTensorP T b : Real)

/-- The q-pilot root formula log is exactly the root hull formula log at the
minimal sector. -/
theorem qPilotRootRegionFormulaLog_eq_rootThetaHullFormulaLog :
    qPilotRootRegionFormulaLog T b = rootThetaHullFormulaLog T b := rfl

end LeanFormal.IUT.XiFPaper.QVPilotRootRegionNestingActual

end
