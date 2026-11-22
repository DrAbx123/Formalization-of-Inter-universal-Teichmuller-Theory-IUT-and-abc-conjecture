import tmp.sheaf.xif.paper.S1004QVFamFiniteLinearizationActual
import tmp.sheaf.xif.paper.S923RInteriorNonemptyActual
import tmp.sheaf.xif.paper.S973QPilotTensorImagePositivityActual

/-! # S1007: positivity of the S1004 finite qPilot image

qPilotPaperRegion has nonempty interior when the fractional lattice F(cRoot)
is open (S923).  s1004E is a finite-dimensional Qp-linear equivalence, hence
an open map/homeomorphism; it carries interior to interior.  The finite Haar
is open-positive, so the image has positive measure.  The exact minimal input
is openness of F(cRoot). -/

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1007QPilotPositivityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S921RQpilotPaperRegionPositivityActual
open LeanFormal.IUT.XiFPaper.S923RInteriorNonemptyActual
open LeanFormal.IUT.XiFPaper.S973QPilotTensorImagePositivityActual
open LeanFormal.IUT.XiFPaper.S1004QVFamFiniteLinearizationActual
open MeasureTheory Topology

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- s1004E is an open map (finite-dimensional linear homeomorphism). -/
theorem s1007E_isOpenMap :
    IsOpenMap (s1004E (l := l) T b) := by
  let eCLE := (s1004E (l := l) T b).toContinuousLinearEquiv
  exact eCLE.toHomeomorph.isOpenMap

/-- Nonempty interior of the qPilot region gives nonempty interior of its
S1004 image. -/
theorem s1007QPilotImage_interior_nonempty_of_open
    (hopen : S923FractionalLatticeOpen (l := l) T b) :
    (interior (s1004QPilotImage (l := l) T b)).Nonempty := by
  have hR : S921RInteriorNonempty (l := l) T b :=
    s923R_interior_nonempty_of_open (l := l) T b hopen
  rcases hR with ⟨x, hx⟩
  refine ⟨s1004E (l := l) T b x, ?_⟩
  exact (s1007E_isOpenMap (l := l) T b).image_interior_subset
    (qPilotPaperRegion (l := l) T b) ⟨x, hx, rfl⟩

/-- Actual positivity of the S1004 finite qPilot image. -/
theorem s1007QPilotImage_measure_pos_of_open
    (hopen : S923FractionalLatticeOpen (l := l) T b) :
    0 < (s1004H (l := l) T b).measure
      (s1004QPilotImage (l := l) T b) := by
  let H := s1004H (l := l) T b
  haveI : Measure.IsAddHaarMeasure H.measure := H.isAddHaar
  haveI : Measure.IsOpenPosMeasure H.measure := inferInstance
  have hne : H.measure (interior (s1004QPilotImage (l := l) T b)) ≠ 0 :=
    Measure.IsOpenPosMeasure.open_pos
      (interior (s1004QPilotImage (l := l) T b))
      isOpen_interior
      (s1007QPilotImage_interior_nonempty_of_open (l := l) T b hopen)
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hne) (measure_mono interior_subset)

/-- Exact minimal positivity input. -/
def S1007QPilotPositivityInput : Prop :=
  S923FractionalLatticeOpen (l := l) T b

/-- Exact minimal positivity goal. -/
def S1007QPilotMeasurePositive : Prop :=
  0 < (s1004H (l := l) T b).measure
    (s1004QPilotImage (l := l) T b)

end LeanFormal.IUT.XiFPaper.S1007QPilotPositivityActual
end
