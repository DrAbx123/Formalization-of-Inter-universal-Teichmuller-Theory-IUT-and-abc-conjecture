import tmp.sheaf.xif.paper.S968FinalTensorInequalityCor312Actual
import tmp.sheaf.xif.paper.S923RInteriorNonemptyActual

/-! # S973: positivity of the qPilot tensor image

`qPilotPaperImageInLValued` is the image of the qPilot region under
`qVFamToLValued`.  Under a carrier topology and additive Haar measure, an
open map plus nonempty interior of the qPilot region gives positive measure.
The exact minimal alternative is nonempty interior of the image. -/

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S973QPilotTensorImagePositivityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedThetaIndHullActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S962TensorPacketPaperInequalityActual
open LeanFormal.IUT.XiFPaper.S968FinalTensorInequalityCor312Actual
open LeanFormal.IUT.XiFPaper.S921RQpilotPaperRegionPositivityActual
open LeanFormal.IUT.XiFPaper.S923RInteriorNonemptyActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable [TopologicalSpace (FinalLValuedCarrier T b)]
variable [MeasurableSpace (FinalLValuedCarrier T b)]
variable [BorelSpace (FinalLValuedCarrier T b)]
variable (mu : Measure (FinalLValuedCarrier T b))
variable [Measure.IsAddHaarMeasure mu]

/-- Exact minimal positivity condition: the qPilot tensor image has nonempty
interior. -/
def S973QPilotImageInteriorNonempty : Prop :=
  (interior (qPilotPaperImageInLValued (l := l) T b)).Nonempty

/-- Interior nonempty gives positive Haar measure. -/
theorem s973QPilotImage_measure_pos_of_interior
    (h : S973QPilotImageInteriorNonempty (l := l) T b) :
    0 < mu (qPilotPaperImageInLValued (l := l) T b) := by
  haveI : Measure.IsOpenPosMeasure mu := inferInstance
  have hne : mu (interior (qPilotPaperImageInLValued (l := l) T b)) ≠ 0 :=
    Measure.IsOpenPosMeasure.open_pos
      (interior (qPilotPaperImageInLValued (l := l) T b)) isOpen_interior h
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hne) (measure_mono interior_subset)

/-- Open map + nonempty interior of the qPilot region give the exact
interior condition for the image. -/
theorem s973QPilotImage_interior_of_open
    (hopen : IsOpenMap (qVFamToLValued (l := l) T b))
    (hR : S921RInteriorNonempty (l := l) T b) :
    S973QPilotImageInteriorNonempty (l := l) T b := by
  rcases hR with ⟨x, hx⟩
  have hx' : x ∈ interior (qPilotPaperRegion (l := l) T b) := by
    simpa [s914R] using hx
  refine ⟨qVFamToLValued (l := l) T b x, ?_⟩
  exact IsOpenMap.image_interior_subset hopen (qPilotPaperRegion (l := l) T b)
    ⟨x, hx', rfl⟩

theorem s973QPilotImage_measure_pos_of_open
    (hopen : IsOpenMap (qVFamToLValued (l := l) T b))
    (hR : S921RInteriorNonempty (l := l) T b) :
    0 < mu (qPilotPaperImageInLValued (l := l) T b) :=
  s973QPilotImage_measure_pos_of_interior (l := l) T b mu
    (s973QPilotImage_interior_of_open (l := l) T b hopen hR)

/-- D-specific exact positivity condition, using the carrier topology stored in
FinalLTensorLogVolumeData. -/
noncomputable def S973DQPilotImageInteriorNonempty
    (D : FinalLTensorLogVolumeData (l := l) T b) : Prop :=
  letI := D.topologicalSpace
  letI := D.measurableSpace
  letI := D.borelSpace
  letI := D.isTopologicalAddGroup
  letI := D.locallyCompactSpace
  (interior (qPilotPaperImageInLValued (l := l) T b)).Nonempty

/-- D-specific positivity from the exact interior condition. -/
theorem s973DQPilotImage_measure_pos_of_interior
    (D : FinalLTensorLogVolumeData (l := l) T b)
    (h : S973DQPilotImageInteriorNonempty (l := l) T b D) :
    0 < D.measure (qPilotPaperImageInLValued (l := l) T b) := by
  letI := D.topologicalSpace
  letI := D.measurableSpace
  letI := D.borelSpace
  letI := D.isTopologicalAddGroup
  letI := D.locallyCompactSpace
  letI := D.isAddHaar
  exact s973QPilotImage_measure_pos_of_interior (l := l) T b D.measure h

end LeanFormal.IUT.XiFPaper.S973QPilotTensorImagePositivityActual

end
