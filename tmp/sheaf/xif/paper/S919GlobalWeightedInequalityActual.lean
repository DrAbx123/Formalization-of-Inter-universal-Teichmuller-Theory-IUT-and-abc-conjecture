import tmp.sheaf.xif.paper.S874GlobalInterfaceFillActual
import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-- Weighted sum of per-b V with the actual Vbad weights. -/
noncomputable def weightedPaperV
    (V : (b : Bad (nativePlaceSelection T)) → Real) : Real :=
  ∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b * V b

/-- Pure weighted monotonicity: nonnegative weights preserve per-b inequalities. -/
theorem weightedPaperV_mono
    {R S : (b : Bad (nativePlaceSelection T)) → Real}
    (h : ∀ b : Bad (nativePlaceSelection T), R b ≤ S b) :
    weightedPaperV (l := l) T R ≤ weightedPaperV (l := l) T S := by
  unfold weightedPaperV
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left (h b) (nativeBadLocalWeight_nonneg T b)

/-- Concrete per-b V: qPilot paper region log. -/
noncomputable def perBVR (b : Bad (nativePlaceSelection T)) : Real :=
  qPilotPaperRegionLog (l := l) T b (mu b)

/-- Concrete per-b V: nonzero theta hull log. -/
noncomputable def perBVS (b : Bad (nativePlaceSelection T)) : Real :=
  paperRootThetaHullLogNonzero (l := l) T b (mu b)

/-- Global weighted inequality from per-b V(R_b) ≤ V(S_b).  No equality, no
scaling data, no hull-log formula is used. -/
theorem globalWeightedInequality_of_perB
    (h : ∀ b : Bad (nativePlaceSelection T), perBVR (l := l) T mu b ≤
      perBVS (l := l) T mu b) :
    weightedPaperV (l := l) T (perBVR (l := l) T mu) ≤
      weightedPaperV (l := l) T (perBVS (l := l) T mu) :=
  weightedPaperV_mono (l := l) T h

/-- Exact minimal side condition: the per-b inequality. -/
def PerBGlobalWeightedHypothesis : Prop :=
  ∀ b : Bad (nativePlaceSelection T), perBVR (l := l) T mu b ≤
    perBVS (l := l) T mu b

theorem globalWeightedInequality_actual
    (h : PerBGlobalWeightedHypothesis (l := l) T mu) :
    weightedPaperV (l := l) T (perBVR (l := l) T mu) ≤
      weightedPaperV (l := l) T (perBVS (l := l) T mu) :=
  globalWeightedInequality_of_perB (l := l) T mu h

end LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual

end
