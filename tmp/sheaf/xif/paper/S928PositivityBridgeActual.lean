import tmp.sheaf.xif.paper.S918RQpilotVolumeLeSHullActual
import tmp.sheaf.xif.paper.S923RInteriorNonemptyActual
import tmp.sheaf.xif.paper.S921RQpilotPaperRegionPositivityActual

/-! # S928: positivity bridge for S918

S918RMeasurePosRequired is proved from S921's exact interior condition, and
from S923's exact openness of the fractional lattice F(cRoot).  In the latter
case V(R) <= V(S) follows from S918 with no equality and no spectral/order
identification.  Openness of F(cRoot) is the exact minimal remaining input. -/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S928PositivityBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open LeanFormal.IUT.XiFPaper.S918RQpilotVolumeLeSHullActual
open LeanFormal.IUT.XiFPaper.S921RQpilotPaperRegionPositivityActual
open LeanFormal.IUT.XiFPaper.S923RInteriorNonemptyActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]

/-- S921 nonempty interior gives S918RMeasurePosRequired. -/
theorem s928RMeasurePosRequired_of_interior
    (h : S921RInteriorNonempty (l := l) T b) :
    S918RMeasurePosRequired (l := l) T b mu :=
  s921R_measure_pos_of_interior (l := l) T b mu h

/-- S923 openness of F(cRoot) gives S918RMeasurePosRequired. -/
theorem s928RMeasurePosRequired_of_F_open
    (hopen : S923FractionalLatticeOpen (l := l) T b) :
    S918RMeasurePosRequired (l := l) T b mu :=
  s928RMeasurePosRequired_of_interior (l := l) T b mu
    (s923R_interior_nonempty_of_open (l := l) T b hopen)

/-- Main inequality V(R) <= V(S) from openness of F(cRoot). -/
theorem s928V_R_le_V_S_of_F_open
    (hopen : S923FractionalLatticeOpen (l := l) T b) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (s914R (l := l) T b) ≤
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (s914S (l := l) T b) :=
  s918V_R_le_V_S (l := l) T b mu
    (s928RMeasurePosRequired_of_F_open (l := l) T b mu hopen)

/-- Exact minimal remaining input: openness of the fractional lattice F(cRoot). -/
def S928FractionalLatticeOpenRequired : Prop :=
  S923FractionalLatticeOpen (l := l) T b

end LeanFormal.IUT.XiFPaper.S928PositivityBridgeActual

end
