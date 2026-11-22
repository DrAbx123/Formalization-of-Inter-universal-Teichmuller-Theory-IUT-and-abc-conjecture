import tmp.sheaf.xif.paper.S929RQpilotPaperSHullFinalActual
import tmp.sheaf.xif.paper.S919GlobalWeightedInequalityActual
import tmp.sheaf.xif.paper.S916PaperMultiradialSActual
import tmp.sheaf.xif.paper.S914PaperLVExInstantiationActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
/-! # S941: paper-faithful Corollary 3.12 contract
The object is the paper S = closure(theta union + actual Ind image), not
theta-only.  The contract records the actual D fields (nonempty Ind image and
Ind1/Ind2/Ind3 transfer), actual R ⊆ S, per-b V inequality, and global weights.
No empty Ind image is used. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S941PaperCor312FaithfulContractActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S922ModelHullPaperSHullInequalityActual
open LeanFormal.IUT.XiFPaper.S929RQpilotPaperSHullFinalActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
variable (D : ∀ b : Bad (nativePlaceSelection T), PaperIndImageData (l := l) T b)
/-- Paper S is exactly the closure of theta union + actual Ind image. -/
def PaperCor312FaithfulObject : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    paperSHull (l := l) T b (D b) =
      closure (paperRootThetaImageNZ (l := l) T b ∪ (D b).indImage)
theorem paperCor312_object_actual : PaperCor312FaithfulObject (l := l) T D :=
  fun _ => rfl
/-- Exact boundedness of each actual Ind image. -/
def S941IndImageBounded : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    S922IndImageBounded (l := l) T b (D b)
/-- Actual D fields: nonempty Ind image and the three transfer obligations. -/
def PaperCor312ActualD : Prop :=
  (∀ b : Bad (nativePlaceSelection T), (D b).indImage.Nonempty) ∧
    (∀ b : Bad (nativePlaceSelection T), (D b).ind1_transfer) ∧
    (∀ b : Bad (nativePlaceSelection T), (D b).ind2_transfer) ∧
    (∀ b : Bad (nativePlaceSelection T), (D b).ind3_transfer) ∧
    S941IndImageBounded (l := l) T D
/-- Paper-faithful Cor 3.12 contract. -/
def PaperCor312Faithful : Prop :=
  PaperCor312FaithfulObject (l := l) T D ∧
    PaperCor312ActualD (l := l) T D
noncomputable def s941VR (b : Bad (nativePlaceSelection T)) : Real :=
  s929V_R (l := l) T b (mu b)
noncomputable def s941VS (b : Bad (nativePlaceSelection T)) : Real :=
  s929V_S (l := l) T b (mu b) (D b)
/-- Global weighted paper inequality. -/
def PaperCor312GlobalInequality : Prop :=
  weightedPaperV (l := l) T (s941VR (l := l) T mu) ≤
    weightedPaperV (l := l) T (s941VS (l := l) T mu D)
/-- Actual containment R ⊆ paper S. -/
theorem paperCor312_R_subset_paperS :
    ∀ b : Bad (nativePlaceSelection T),
      s914R (l := l) T b ⊆ paperSHull (l := l) T b (D b) :=
  fun b => by
    rw [s914R_eq_modelHull (l := l) T b]
    exact modelHull_subset_paperSHull (l := l) T b (D b)
/-- Paper-faithful conditional Cor 3.12: per-b V inequality and global weights. -/
theorem paperCor312_of_actualD
    (F : PaperCor312Faithful (l := l) T D) :
    (∀ b : Bad (nativePlaceSelection T),
      s941VR (l := l) T mu b ≤ s941VS (l := l) T mu D b) ∧
    PaperCor312GlobalInequality (l := l) T mu D := by
  have hD : S941IndImageBounded (l := l) T D := F.2.2.2.2.2
  have hPerB : ∀ b : Bad (nativePlaceSelection T),
      s941VR (l := l) T mu b ≤ s941VS (l := l) T mu D b := by
    intro b
    exact s929V_R_le_V_S (l := l) T b (mu b) (D b) (hD b)
  refine ⟨hPerB, ?_⟩
  exact weightedPaperV_mono (l := l) T hPerB
end LeanFormal.IUT.XiFPaper.S941PaperCor312FaithfulContractActual
