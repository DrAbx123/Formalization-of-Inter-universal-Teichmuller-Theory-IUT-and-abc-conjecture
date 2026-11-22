import tmp.sheaf.xif.paper.S779RootHullNonzeroFixActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.RootHullMeasureActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual

/-! # S1063: correct per-b inequality qPilotClassicalLog <= paperRootThetaHullLogNonzero

The qPilot region uses cNorm = qVFamNormalizedCoefficient (the qVFamily order),
while the paper nonzero hull uses cRoot = qVFamPaperRootCoefficient =
cNorm/(2l).  The actual coefficient inequality cRoot <= cNorm gives
  qPilotNormRegion ⊆ paperRootThetaHullNonzero,
not merely containment in the full hull.  Positivity of qPilotNormRegion is
actual (RootHullMeasure), and finiteness of the paper nonzero hull follows
from its containment in rootNormHull.  Hence normalized-log monotonicity gives
the per-b inequality.  No qPilotPaperRegion substitution. -/

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1063PerBQPilotPaperNonzeroActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open MeasureTheory Topology

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]

/-- Paper root coefficient = rootHalfCoefficient. -/
theorem s1063_paperCoeff_eq_rootHalf :
    paperRootCoefficientFamily (l := l) T b = rootHalfCoefficient (l := l) T b := by
  funext i
  unfold paperRootCoefficientFamily qVFamPaperRootCoefficient rootHalfCoefficient
    rootNormCoefficient qVFamNormalizedCoefficient qVFamTensorCoefficient
    qVFamNormalizedCoefficientFamily paperRootCoefficientFamily
  ring

/-- Actual containment of the qPilot region in the paper nonzero hull. -/
theorem s1063_qPilot_subset_paperNonzero :
    qPilotNormRegion (l := l) T b ⊆ paperRootThetaHullNonzero (l := l) T b := by
  intro x hx
  unfold paperRootThetaHullNonzero rootThetaHullNonzero rootThetaImageSetNonzero
  apply subset_closure
  apply Set.mem_iUnion.mpr
  refine ⟨⟨oneLabel l, oneLabel_ne_zero (l := l) (oneLabel l)
    (gaussExponent_oneLabel l)⟩, ?_⟩
  have hlat : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple (rootNormCoefficient (l := l) T b) ≤
      arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple (fun i => (gaussExponent (oneLabel l).1).toNat *
        paperRootCoefficientFamily (l := l) T b i) := by
    apply arithmeticTupleFractionalLattice_mono
    intro i
    rw [gaussExponent_oneLabel]
    simp only [Nat.cast_one, one_mul]
    unfold paperRootCoefficientFamily rootNormCoefficient
    exact qVFamPaperRootCoefficient_le_normalized (l := l) T b
  exact (mul_le_mul' hlat le_rfl) hx

/-- Finiteness of the paper nonzero hull. -/
theorem s1063_paperNonzero_measure_lt_top :
    mu (paperRootThetaHullNonzero (l := l) T b) < ⊤ := by
  have hsub : paperRootThetaHullNonzero (l := l) T b ⊆ rootNormHull (l := l) T b := by
    unfold paperRootThetaHullNonzero rootNormHull rootThetaHullNonzero rootThetaHull
      rootThetaImageSetNonzero rootThetaImageSet
    rw [s1063_paperCoeff_eq_rootHalf (l := l) T b]
    apply closure_mono
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
    exact Set.mem_iUnion.mpr ⟨j.1, hj⟩
  exact lt_of_le_of_lt (measure_mono hsub) (rootNormHull_measure_lt_top (l := l) T b mu)

/-- Positivity of the qPilot region. -/
theorem s1063_qPilot_measure_pos :
    0 < mu (qPilotNormRegion (l := l) T b) :=
  (qPilotNormRegion_measure_pos_lt_top (l := l) T b mu).1

/-- Correct per-b inequality, using the paper nonzero hull. -/
theorem s1063PerBInequality :
    perBQPilotLog (l := l) T b ≤
      paperRootThetaHullLogNonzero (l := l) T b Measure.addHaar := by
  unfold perBQPilotLog qPilotClassicalLog paperRootThetaHullLogNonzero
  change arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
      Measure.addHaar (qPilotNormRegion (l := l) T b) ≤
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
      Measure.addHaar (paperRootThetaHullNonzero (l := l) T b)
  exact arithmeticTupleNormalizedLogVolume_mono
    (qVFamTensorPlaces T b) qVFamTensorTuple Measure.addHaar
    (s1063_qPilot_subset_paperNonzero (l := l) T b)
    (s1063_qPilot_measure_pos (l := l) T b Measure.addHaar)
    (s1063_paperNonzero_measure_lt_top (l := l) T b Measure.addHaar)

end LeanFormal.IUT.XiFPaper.S1063PerBQPilotPaperNonzeroActual

end
