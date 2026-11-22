import tmp.sheaf.xif.paper.S779RootHullNonzeroFixActual
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual

/-! # S805: replace zero-inclusive root hull/log by S779 nonzero hull/log

Actual set containment qPilotPaperRegion ⊆ paperRootThetaHullNonzero is
retained.  The log identification is an exact bridge, not the old
zero-inclusive paperRootThetaHullLog theorem.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

/-- Paper qPilot region: j=1 theta region at paper coefficient order/(2l). -/
noncomputable def qPilotPaperRegion : Set (qVFamTensorBlock T b) :=
  thetaTensorScaledRegion (qVFamTensorPlaces T b) qVFamTensorTuple
    (paperRootCoefficientFamily (l := l) T b)

theorem qPilotPaperRegion_eq_rootThetaRegion_one :
    qPilotPaperRegion (l := l) T b =
      rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily (l := l) T b) (oneLabel l) := by
  unfold qPilotPaperRegion rootThetaRegion
  congr 1
  funext i
  simp [paperRootCoefficientFamily, gaussExponent_oneLabel]

theorem qPilotPaperRegion_subset_nonzeroHull :
    qPilotPaperRegion (l := l) T b ⊆
      paperRootThetaHullNonzero (l := l) T b := by
  rw [qPilotPaperRegion_eq_rootThetaRegion_one]
  unfold paperRootThetaHullNonzero rootThetaHullNonzero rootThetaImageSetNonzero
  exact (Set.subset_iUnion
    (fun j : NonzeroLabel (l := l) =>
      rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily (l := l) T b) j.1)
    ⟨oneLabel l, by rw [oneLabel_val]; norm_num⟩).trans
    subset_closure

structure NonzeroHullContainmentData where
  qPilotImage : Set (qVFamTensorBlock T b)
  qPilotImage_eq : qPilotImage = qPilotPaperRegion (l := l) T b
  hull : Set (qVFamTensorBlock T b)
  hull_eq : hull = paperRootThetaHullNonzero (l := l) T b
  containment : qPilotImage ⊆ hull

noncomputable def nonzeroHullContainmentData :
    NonzeroHullContainmentData (l := l) T b where
  qPilotImage := qPilotPaperRegion (l := l) T b
  qPilotImage_eq := rfl
  hull := paperRootThetaHullNonzero (l := l) T b
  hull_eq := rfl
  containment := qPilotPaperRegion_subset_nonzeroHull (l := l) T b

noncomputable def qPilotPaperRegionLog : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
    mu (qPilotPaperRegion (l := l) T b)

def NonzeroHullLogBridge : Prop :=
  qPilotPaperRegionLog (l := l) T b mu =
    paperRootThetaHullLogNonzero (l := l) T b mu

def NonzeroHullLogBridgeRequired : Prop :=
  NonzeroHullLogBridge (l := l) T b mu

def S734CorrectedNonzeroBridge : Prop :=
  S733CorrectedHullLogNonzeroCondition (l := l) T b

def S739CorrectedNonzeroBridge : Prop :=
  S739PaperOrderLogNonzeroCondition (l := l) T b

end LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
end
