import tmp.sheaf.xif.paper.S1086PerBQ1URootHullActual
import tmp.sheaf.xif.paper.S1091QPilotQ1UPositivityActual
import tmp.sheaf.xif.paper.S919GlobalWeightedInequalityActual

/-! # S1103: weighted global from the per-b q[1u] inequality

The canonical q[1u] per-b log is `qPilotQ1ULogHaar`; the root-stack theta
hull per-b log is `rootStackPaperThetaHullLog`.  Weighted summation with the
actual nonnegative weights `nativeBadLocalWeight` preserves the per-b
inequality.  S1102 is not present in the tree; this file records the exact
per-b hypothesis and the actual weighted-global reduction. -/

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1103Q1UGlobalWeightedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S1072CanonicalQ1URegionActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open LeanFormal.IUT.XiFPaper.S1086PerBQ1URootHullActual
open LeanFormal.IUT.XiFPaper.S1091QPilotQ1UPositivityActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open MeasureTheory Topology

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Per-b canonical q[1u] log <= root-stack paper theta hull log. -/
def S1103PerBInequality : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    qPilotQ1ULogHaar (l := l) T b ≤ rootStackPaperThetaHullLog (l := l) T b

/-- Weighted global inequality from the per-b inequality. -/
theorem s1103WeightedGlobal_of_perB
    (h : S1103PerBInequality (l := l) T) :
    weightedPaperV (l := l) T (fun b => qPilotQ1ULogHaar (l := l) T b) ≤
      weightedPaperV (l := l) T (fun b => rootStackPaperThetaHullLog (l := l) T b) :=
  weightedPaperV_mono (l := l) T h

/-- Exact weighted-global target. -/
def S1103WeightedGlobalGoal : Prop :=
  weightedPaperV (l := l) T (fun b => qPilotQ1ULogHaar (l := l) T b) ≤
    weightedPaperV (l := l) T (fun b => rootStackPaperThetaHullLog (l := l) T b)

/-- Exact minimum: the per-b inequality. -/
def S1103ExactMinimum : Prop :=
  S1103PerBInequality (l := l) T

theorem s1103WeightedGlobal_of_exact
    (h : S1103ExactMinimum (l := l) T) :
    S1103WeightedGlobalGoal (l := l) T :=
  s1103WeightedGlobal_of_perB (l := l) T h

end LeanFormal.IUT.XiFPaper.S1103Q1UGlobalWeightedActual

end
