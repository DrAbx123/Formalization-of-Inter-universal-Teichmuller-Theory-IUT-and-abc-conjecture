/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S800LeastLambdaOHullActual
import tmp.sheaf.xif.paper.S778PaperQPilotHalfRegionActual
import tmp.sheaf.xif.paper.RootHullMeasureActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.S920SHullFinitenessActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegerTensorComparison
import Mathlib.Tactic

/-! # Block-level paper target: S800 least-hull positivity/finiteness

| field | value |
|---|---|---|
| Status | unconditional qPilotPaperRegionLog <= paperHullLog on T; finiteness via the constant-zero candidate F(0)O = R*O = R; positivity via qPilotPaperRegion subset least hull. |
| GAP | S800 paperHullLog is the least lambda-O hull at rootHalfCoefficient with SignedLabel (includes j=0), not the P4 paperFaithful NonzeroHull; no identification. |
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperBlockTargetActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S800LeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S778PaperQPilotHalfRegionActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

theorem lambdaORegion_zero_mem_candidate :
    lambdaORegion (l := l) T b (fun _ => (0 : Real)) ∈
      candidateHulls (l := l) T b (paperPossibleImages (l := l) T b) := by
  refine ⟨⟨(fun _ => (0 : Real)), rfl⟩, ?_⟩
  intro x hx
  unfold paperPossibleImages at hx
  rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
  unfold lambdaORegion qPilotClassicalRegion
  unfold rootThetaRegion at hj
  have hlat : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple (fun i => (gaussExponent j.1).toNat *
        rootHalfCoefficient (l := l) T b i) ≤
      arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple (fun _ => (0 : Real)) := by
    apply arithmeticTupleFractionalLattice_mono
    intro i
    exact rootHalfCoefficient_thetaCoeff_nonneg (l := l) T b i j
  exact (mul_le_mul' hlat le_rfl) hj

theorem leastLambdaOHull_subset_lambdaORegion_zero :
    leastLambdaOHull (l := l) T b (paperPossibleImages (l := l) T b) ⊆
      lambdaORegion (l := l) T b (fun _ => (0 : Real)) :=
  leastLambdaOHull_subset_candidate (l := l) T b
    (paperPossibleImages (l := l) T b)
    (lambdaORegion (l := l) T b (fun _ => (0 : Real)))
    (lambdaORegion_zero_mem_candidate (l := l) T b)

theorem lambdaORegion_zero_measure_lt_top :
    mu (lambdaORegion (l := l) T b (fun _ => (0 : Real))) < ⊤ := by
  unfold lambdaORegion qPilotClassicalRegion
  rw [arithmeticTupleFractionalLattice_zero]
  have hmul : arithmeticTupleValuationIntegerLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple * arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple =
      arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :=
    arithmeticTupleValuationIntegerLattice_mul_holomorphicLattice
      (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
  rw [hmul]
  rw [coefficient_arithmeticTupleHolomorphicLattice]
  exact (isCompact_arithmeticTupleCanonicalRegions
    (qVFamTensorPlaces T b) qVFamTensorTuple).2.measure_lt_top

theorem paperHull_measure_lt_top :
    mu (leastLambdaOHull (l := l) T b (paperPossibleImages (l := l) T b)) < ⊤ :=
  lt_of_le_of_lt (measure_mono (leastLambdaOHull_subset_lambdaORegion_zero (l := l) T b))
    (lambdaORegion_zero_measure_lt_top (l := l) T b mu)

theorem qPilotPaperRegionLog_le_paperHullLog_unconditional :
    qPilotPaperRegionLog (l := l) T b mu ≤ paperHullLog (l := l) T b mu :=
  qPilotPaperRegionLog_le_paperHullLog (l := l) T b mu
    (qPilotPaperRegion_measure_pos (l := l) T b mu)
    (paperHull_measure_lt_top (l := l) T b mu)

def rows : List (String × String × String) :=
  [ ("lambdaORegion_zero_mem_candidate", "zero candidate contains all root regions", "PROVED"),
    ("lambdaORegion_zero_measure_lt_top", "F(0)O = R*O = R finite", "PROVED"),
    ("paperHull_measure_lt_top", "finite", "PROVED"),
    ("qPilotPaperRegionLog_le_paperHullLog_unconditional", "S800 pos/fin discharged", "PROVED"),
    ("P4 NonzeroHull identification", "different hull; not used", "GAP") ]

theorem rows_length : rows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PaperBlockTargetActual

end