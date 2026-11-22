import tmp.sheaf.xif.paper.S908ORExpansionContainmentActual

/-! # S914: instantiate the S907/S908 LVEx/OR-expansion abstraction with paper data

R = qPilotPaperRegion
S = paperRootThetaHullNonzero
gluing scale = (2l)/order(c_norm).

The actual containment R ⊆ S is S908's OR-expansion data.  Strictness
S > R is recorded as an exact minimal proposition; no boundary point is
fabricated. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S908ORExpansionContainmentActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]

/-- R: the paper qPilot region. -/
noncomputable def s914R : Set (qVFamTensorBlock T b) :=
  qPilotPaperRegion (l := l) T b

/-- S: the nonzero paper root theta hull. -/
noncomputable def s914S : Set (qVFamTensorBlock T b) :=
  paperRootThetaHullNonzero (l := l) T b

/-- Actual R ⊆ S from S908. -/
theorem s914R_subset_S : s914R (l := l) T b ⊆ s914S (l := l) T b := by
  unfold s914R s914S
  exact paperQPilot_subset_nonzeroHull (l := l) T b

/-- Actual LVEx/OR-expansion comparison via normalized log-volume. -/
theorem s914MuLogComparison
    (hpos : 0 < mu (s914R (l := l) T b))
    (hfin : mu (s914S (l := l) T b) < ⊤) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (s914R (l := l) T b) ≤
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (s914S (l := l) T b) :=
  arithmeticTupleNormalizedLogVolume_mono (qVFamTensorPlaces T b) qVFamTensorTuple
    mu (s914R_subset_S (l := l) T b) hpos hfin

/-- Exact strictness: paper S is strictly larger than R. -/
def S914StrictHullGap : Prop :=
  ∃ x : qVFamTensorBlock T b, x ∈ s914S (l := l) T b ∧
    x ∉ s914R (l := l) T b

/-- Exact minimal statement needed for the strict LVEx/OR-expansion conclusion. -/
def S914StrictHullGapRequired : Prop :=
  S914StrictHullGap (l := l) T b

end LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual