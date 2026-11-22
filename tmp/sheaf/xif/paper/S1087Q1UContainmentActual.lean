import tmp.sheaf.xif.paper.S1072CanonicalQ1URegionActual
import tmp.sheaf.xif.paper.S1073RootStackPaperThetaHullActual
import tmp.sheaf.xif.paper.S1082LambdaOPositivityExactActual
/-! # S1087: actual reduction of q[1u] image containment to coefficient comparison
qPilotQ1URegion = F(qVFamPureCoefficient)*O_hol, root hull = F(cRoot)*O_hol
with cRoot = order/(2l).  If cRoot <= qVFamPureCoefficient coordinatewise, the
fractional-lattice order reverses and gives the region/hull containment. -/
noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S1087Q1UContainmentActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S1072CanonicalQ1URegionActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open MeasureTheory Topology
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
/-- Exact coefficient comparison: theta root cRoot <= canonical q[1u] coefficient. -/
def S1087CoeffLe : Prop :=
  ∀ i : qVFamTensorV,
    paperRootCoefficientFamily (l := l) T b i ≤ qVFamPureCoefficient T b i
/-- Coefficient comparison gives the region containment. -/
theorem s1087RegionContainment
    (hc : S1087CoeffLe (l := l) T b) :
    qPilotQ1URegion (l := l) T b ⊆
      paperLambdaORegion (l := l) T b (paperRootCoefficientFamily (l := l) T b) := by
  intro x hx
  unfold qPilotQ1URegion at hx
  unfold paperLambdaORegion
  have hF : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple (qVFamPureCoefficient T b) ≤
      arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b) :=
    arithmeticTupleFractionalLattice_mono
      (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
      (a := paperRootCoefficientFamily (l := l) T b)
      (b := qVFamPureCoefficient T b) hc
  exact (Submodule.mul_le.mpr (fun y hy z hz => Submodule.mul_mem_mul (hF hy) hz)) hx
/-- Image containment in the root-stack paper theta hull. -/
theorem s1087ImageContainment
    (hc : S1087CoeffLe (l := l) T b) :
    rootStackEmbedding (l := l) T b '' qPilotQ1URegion (l := l) T b ⊆
      rootStackPaperThetaHull (l := l) T b := by
  unfold rootStackPaperThetaHull
  exact Set.image_mono (s1087RegionContainment (l := l) T b hc)
/-- Exact minimum for S1086 containment. -/
def S1087ExactMinimum : Prop := S1087CoeffLe (l := l) T b
end LeanFormal.IUT.XiFPaper.S1087Q1UContainmentActual
