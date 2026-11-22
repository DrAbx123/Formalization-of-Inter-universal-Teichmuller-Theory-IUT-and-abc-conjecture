import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.SignedLabelOneActual
import tmp.sheaf.xif.paper.S810LeastHullPaperCarrierActual

-- S790: finite root-stack carrier -> paper qPilot/Theta hull.
-- The root-stack root divisor is paper order/(2l); the qPilot paper
-- region equals the j=1 paper root theta region and is contained in the
-- paper root hull.  Haar/log target remains exact.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S790StackToPaperQPilotThetaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.S810LeastHullPaperCarrierActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory
open scoped BigOperators

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem stackRootSection_divisor_order :
    stackDivisorSection (l := l) T b (stackRootSection (l := l) T b) =
      Multiplicative.ofAdd (((qVFamily T b).order : Real) / (2 * l.value)) :=
  rfl

theorem stackQSection_divisor_order :
    stackDivisorSection (l := l) T b (stackQSection (l := l) T b) =
      Multiplicative.ofAdd ((qVFamily T b).order : Real) :=
  rfl

/-- Paper-order coefficient family order/(2l). -/
noncomputable def paperOrderCoefficient : qVFamTensorV → Real :=
  fun _ : qVFamTensorV => ((qVFamily T b).order : Real) / (2 * l.value)

/-- Paper qPilot log at order/(2l). -/
noncomputable def paperStackQPilotLog : Real :=
  -((∑ _ : qVFamTensorV, paperOrderCoefficient (l := l) T b ()) *
    Real.log (qVFamTensorP T b : Real))

theorem paperRootCoefficientFamily_eq_paperOrder (i : qVFamTensorV) :
    paperRootCoefficientFamily T b i = paperOrderCoefficient (l := l) T b i :=
  rfl

/-- The paper qPilot region at order/(2l): F(order/(2l))*O_hol. -/
noncomputable def paperStackQPilotRegion : Set (qVFamTensorBlock T b) :=
  ((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperOrderCoefficient (l := l) T b) *
    arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
      Submodule ℤ_[qVFamTensorP T b] (qVFamTensorBlock T b)) :
    Set (qVFamTensorBlock T b))

/-- The paper theta region at label j=1 equals the qPilot region. -/
theorem paperStackQPilotRegion_eq_thetaRegion_one :
    paperStackQPilotRegion (l := l) T b =
      rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperOrderCoefficient (l := l) T b) (oneLabel l) := by
  unfold paperStackQPilotRegion rootThetaRegion
  rw [gaussExponent_oneLabel]
  simp

theorem paperStackQPilotRegion_subset_paperRootHull :
    paperStackQPilotRegion (l := l) T b ⊆ paperRootThetaHull T b := by
  intro x hx
  unfold paperRootThetaHull rootThetaHull rootThetaImageSet
  apply subset_closure
  exact Set.mem_iUnion.mpr ⟨oneLabel l, by
    have hfun : paperRootCoefficientFamily T b = paperOrderCoefficient (l := l) T b :=
      funext (paperRootCoefficientFamily_eq_paperOrder (l := l) T b)
    simpa [paperStackQPilotRegion_eq_thetaRegion_one (l := l) T b, hfun] using hx⟩

/-- Actual paper target: paper-order qPilot log <= paper root hull log. -/
def PaperStackTarget : Prop :=
  paperStackQPilotLog (l := l) T b ≤
    paperRootThetaHullLog (l := l) T b Measure.addHaar

/-- Exact Haar-log bridge: qPilot log is the normalized hull log of the
j=1 region and the hull is finite/positive. -/
def PaperStackHaarBridge : Prop :=
  0 < Measure.addHaar (paperStackQPilotRegion (l := l) T b) ∧
    Measure.addHaar (paperRootThetaHull T b) < ⊤

#check stackRootSection_divisor_order
#check paperStackQPilotRegion_eq_thetaRegion_one
#check paperStackQPilotRegion_subset_paperRootHull
#check PaperStackTarget
#check PaperStackHaarBridge


/-- The qPilot paper region is the S810 corrected lambda*O region. -/
theorem paperStackQPilotRegion_eq_corrected :
    paperStackQPilotRegion (l := l) T b =
      S810LeastHullPaperCarrierActual.paperQPilotRegionCorrected (l := l) T b :=
  rfl

/-- Actual containment of the qPilot region in the corrected least hull. -/
theorem paperStackQPilotRegion_subset_leastHull :
    paperStackQPilotRegion (l := l) T b ⊆
      S810LeastHullPaperCarrierActual.paperHullFirstCarrierCorrected (l := l) T b := by
  rw [paperStackQPilotRegion_eq_corrected (l := l) T b]
  exact S810LeastHullPaperCarrierActual.paperQPilotRegionCorrected_subset_least
    (l := l) T b

/-- Exact corrected target: qPilot log vs the least-hull normalized log. -/
def PaperStackTargetLeast : Prop :=
  paperStackQPilotLog (l := l) T b ≤
    S810LeastHullPaperCarrierActual.paperHullFirstLogCorrected (l := l) T b
      Measure.addHaar


end LeanFormal.IUT.XiFPaper.S790StackToPaperQPilotThetaActual

end